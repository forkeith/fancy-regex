// Copyright 2016 The Fancy Regex Authors.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

//! Analysis of regex expressions.

use alloc::string::String;
use alloc::vec::Vec;
use core::cmp::min;

use bit_set::BitSet;

use crate::alloc::string::ToString;
use crate::parse::ExprTree;
use crate::{CompileError, Error, Expr, Result};

#[derive(Debug)]
pub struct Info<'a> {
    pub(crate) start_group: usize,
    pub(crate) end_group: usize,
    pub(crate) min_size: usize,
    pub(crate) const_size: bool,
    pub(crate) hard: bool,
    pub(crate) expr: &'a Expr,
    pub(crate) children: Vec<Info<'a>>,
    pub(crate) min_pos_in_group: usize,
}

impl<'a> Info<'a> {
    pub(crate) fn is_literal(&self) -> bool {
        match *self.expr {
            Expr::Literal { casei, .. } => !casei,
            Expr::Concat(_) => self.children.iter().all(|child| child.is_literal()),
            _ => false,
        }
    }

    pub(crate) fn push_literal(&self, buf: &mut String) {
        match *self.expr {
            // could be more paranoid about checking casei
            Expr::Literal { ref val, .. } => buf.push_str(val),
            Expr::Concat(_) => {
                for child in &self.children {
                    child.push_literal(buf);
                }
            }
            _ => panic!("push_literal called on non-literal"),
        }
    }
}

struct Analyzer<'a> {
    backrefs: &'a BitSet,
    group_ix: usize,
    inside_groups: BitSet,
    subroutine_calls: Vec<BitSet>,
    recursive_subroutines: BitSet,
}

impl<'a> Analyzer<'a> {
    fn visit(&mut self, expr: &'a Expr, min_pos_in_group: usize) -> Result<Info<'a>> {
        let start_group = self.group_ix;
        let mut children = Vec::new();
        let mut min_size = 0;
        let mut const_size = false;
        let mut hard = false;
        match *expr {
            Expr::Assertion(assertion) if assertion.is_hard() => {
                const_size = true;
                hard = true;
            }
            Expr::Empty | Expr::Assertion(_) => {
                const_size = true;
            }
            Expr::Any { .. } => {
                min_size = 1;
                const_size = true;
            }
            Expr::Literal { ref val, casei } => {
                // right now each character in a literal gets its own node, that might change
                min_size = 1;
                const_size = literal_const_size(val, casei);
            }
            Expr::Concat(ref v) => {
                const_size = true;
                let mut pos_in_group = min_pos_in_group;
                for child in v {
                    let child_info = self.visit(child, pos_in_group)?;
                    min_size += child_info.min_size;
                    const_size &= child_info.const_size;
                    hard |= child_info.hard;
                    pos_in_group += child_info.min_size;
                    children.push(child_info);
                }
            }
            Expr::Alt(ref v) => {
                let child_info = self.visit(&v[0], min_pos_in_group)?;
                min_size = child_info.min_size;
                const_size = child_info.const_size;
                hard = child_info.hard;
                children.push(child_info);
                for child in &v[1..] {
                    let child_info = self.visit(child, min_pos_in_group)?;
                    const_size &= child_info.const_size && min_size == child_info.min_size;
                    min_size = min(min_size, child_info.min_size);
                    hard |= child_info.hard;
                    children.push(child_info);
                }
            }
            Expr::Group(ref child) => {
                let group = self.group_ix;
                self.group_ix += 1;
                self.subroutine_calls.push(Default::default());
                self.inside_groups.insert(group);
                let child_info = self.visit(child, 0)?;
                self.inside_groups.remove(group);
                min_size = child_info.min_size;
                const_size = child_info.const_size;
                // If there's a backref to this group, we potentially have to backtrack within the
                // group. E.g. with `(x|xy)\1` and input `xyxy`, `x` matches but then the backref
                // doesn't, so we have to backtrack and try `xy`.
                hard = child_info.hard | self.backrefs.contains(group);
                children.push(child_info);
            }
            Expr::LookAround(ref child, _) => {
                let child_info = self.visit(child, min_pos_in_group)?;
                // min_size = 0
                const_size = true;
                hard = true;
                children.push(child_info);
            }
            Expr::Repeat {
                ref child, lo, hi, ..
            } => {
                let child_info = self.visit(child, min_pos_in_group)?;
                min_size = child_info.min_size * lo;
                const_size = child_info.const_size && lo == hi;
                hard = child_info.hard;
                children.push(child_info);
            }
            Expr::Delegate { size, .. } => {
                // currently only used for empty and single-char matches
                min_size = size;
                const_size = true;
            }
            Expr::Backref { group, .. } => {
                if group == 0 {
                    return Err(Error::CompileError(CompileError::InvalidBackref(group)));
                }
                hard = true;
            }
            Expr::AtomicGroup(ref child) => {
                let child_info = self.visit(child, min_pos_in_group)?;
                min_size = child_info.min_size;
                const_size = child_info.const_size;
                hard = true; // TODO: possibly could weaken
                children.push(child_info);
            }
            Expr::KeepOut => {
                hard = true;
                const_size = true;
            }
            Expr::ContinueFromPreviousMatchEnd => {
                hard = true;
                const_size = true;
            }
            Expr::BackrefExistsCondition(_) => {
                hard = true;
                const_size = true;
            }
            Expr::Conditional {
                ref condition,
                ref true_branch,
                ref false_branch,
            } => {
                hard = true;

                let child_info_condition = self.visit(condition, min_pos_in_group)?;
                let child_info_truth = self.visit(true_branch, min_pos_in_group + child_info_condition.min_size)?;
                let child_info_false = self.visit(false_branch, min_pos_in_group)?;

                min_size = child_info_condition.min_size
                    + min(child_info_truth.min_size, child_info_false.min_size);
                const_size = child_info_condition.const_size
                    && child_info_truth.const_size
                    && child_info_false.const_size
                    // if the condition's size plus the truth branch's size is equal to the false branch's size then it's const size
                    && child_info_condition.min_size + child_info_truth.min_size == child_info_false.min_size;

                children.push(child_info_condition);
                children.push(child_info_truth);
                children.push(child_info_false);
            }
            Expr::SubroutineCall(group) => {
                // make a note that the current group hierarchy calls this subroutine
                for inside_group in self.inside_groups.iter() {
                    self.subroutine_calls[inside_group].insert(group);
                }
                // mark which subroutines are recursive
                if group < self.subroutine_calls.len() {
                    if let Some(_) = self.subroutine_calls[group]
                        .intersection(&self.inside_groups)
                        .next()
                    {
                        self.recursive_subroutines.insert(group);
                        if min_pos_in_group == 0 && group == self.group_ix - 1 {
                            return Err(Error::CompileError(
                                CompileError::LeftRecursiveSubroutineCall(group),
                            ));
                        }
                    }
                }

                return Err(Error::CompileError(CompileError::FeatureNotYetSupported(
                    "Subroutine Call".to_string(),
                )));
            }
            Expr::UnresolvedNamedSubroutineCall { ref name, ix } => {
                return Err(Error::CompileError(
                    CompileError::SubroutineCallTargetNotFound(name.to_string(), ix),
                ));
            }
            Expr::BackrefWithRelativeRecursionLevel { .. } => {
                return Err(Error::CompileError(CompileError::FeatureNotYetSupported(
                    "Backref at recursion level".to_string(),
                )));
            }
        };

        Ok(Info {
            expr,
            children,
            start_group,
            end_group: self.group_ix,
            min_size,
            const_size,
            hard,
            min_pos_in_group,
        })
    }
}
/*
TODO: rewrite based on min pos in group, and do in one pass?
impl SubroutineAnalyzer {
    fn visit(
        &mut self,
        expr: &Expr,
        mut first_child_of_subroutine: bool,
        inside_groups: &mut BitSet,
        ignore_subroutine_calls: bool,
    ) -> Result<()> {
        match expr {
            Expr::Group(ref inner) => {
                let current_subroutine = self.group_ix;
                self.group_ix += 1;
                self.subroutines.insert(current_subroutine, *inner.clone());
                self.subroutine_calls.push(Default::default());
                inside_groups.insert(current_subroutine);
                self.visit(inner, true, inside_groups, false)?;
                inside_groups.remove(current_subroutine);
            }
            // recursively resolve in inner expressions
            Expr::LookAround(inner, _) | Expr::AtomicGroup(inner) => {
                self.visit(
                    inner,
                    first_child_of_subroutine,
                    inside_groups,
                    ignore_subroutine_calls,
                )?;
            }
            Expr::Concat(children) | Expr::Alt(children) => {
                for child in children {
                    self.visit(
                        child,
                        first_child_of_subroutine,
                        inside_groups,
                        ignore_subroutine_calls,
                    )?;
                    first_child_of_subroutine = false;
                }
            }
            Expr::Repeat { child, hi, .. } => {
                self.visit(
                    child,
                    first_child_of_subroutine && *hi > 0,
                    inside_groups,
                    ignore_subroutine_calls || *hi == 0,
                )?;
            }
            Expr::Conditional {
                condition,
                true_branch,
                false_branch,
            } => {
                self.visit(
                    condition,
                    first_child_of_subroutine,
                    inside_groups,
                    ignore_subroutine_calls,
                )?;
                self.visit(true_branch, false, inside_groups, ignore_subroutine_calls)?;
                self.visit(false_branch, false, inside_groups, ignore_subroutine_calls)?;
            }
            Expr::SubroutineCall(group) => {
                // make a note that the current group hierarchy calls this subroutine
                for inside_group in inside_groups.iter() {
                    self.subroutine_calls[inside_group].insert(*group);
                }
                // mark which subroutines are recursive
                if *group < self.subroutine_calls.len() {
                    if let Some(_) = self.subroutine_calls[*group]
                        .intersection(inside_groups)
                        .next()
                    {
                        self.recursive_subroutines.insert(*group);
                        if first_child_of_subroutine && *group == self.group_ix - 1 {
                            return Err(Error::CompileError(
                                CompileError::LeftRecursiveSubroutineCall(*group),
                            ));
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}*/

fn literal_const_size(_: &str, _: bool) -> bool {
    // Right now, regex doesn't do sophisticated case folding,
    // test below will fail when that changes, then we need to
    // do something fancier here.
    true
}

/// Analyze the parsed expression to determine whether it requires fancy features.
pub fn analyze<'a>(tree: &'a ExprTree, start_group: usize) -> Result<Info<'a>> {
    let mut analyzer = Analyzer {
        backrefs: &tree.backrefs,
        group_ix: start_group,
        subroutine_calls: Default::default(),
        inside_groups: BitSet::new(),
        recursive_subroutines: BitSet::new(),
    };

    for group in 0..start_group {
        analyzer.subroutine_calls.push(BitSet::new());
    }

    let analyzed = analyzer.visit(&tree.expr, 0);
    if analyzer.backrefs.contains(0) {
        return Err(Error::CompileError(CompileError::InvalidBackref(0)));
    }
    if let Some(highest_backref) = analyzer.backrefs.into_iter().last() {
        if highest_backref > analyzer.group_ix - start_group
            // if we have an explicit capture group 0, and the highest backref is the number of capture groups
            // then that backref refers to an invalid group
            // i.e. `(a\1)b`   has no capture group 1
            //      `(a(b))\2` has no capture group 2
            || highest_backref == analyzer.group_ix && start_group == 0
        {
            return Err(Error::CompileError(CompileError::InvalidBackref(
                highest_backref,
            )));
        }
    }
    analyzed
}

/// Determine if the expression will always only ever match at position 0.
/// Note that false negatives are possible - it can return false even if it could be anchored.
/// This should therefore only be treated as an optimization.
pub fn can_compile_as_anchored(root_expr: &Expr) -> bool {
    use crate::Assertion;

    match root_expr {
        Expr::Concat(ref children) => match children[0] {
            Expr::Assertion(ref assertion) => *assertion == Assertion::StartText,
            _ => false,
        },
        Expr::Assertion(ref assertion) => *assertion == Assertion::StartText,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::analyze;
    // use super::literal_const_size;
    use crate::{can_compile_as_anchored, CompileError, Error, Expr};

    // #[test]
    // fn case_folding_safe() {
    //     let re = regex::Regex::new("(?i:ß)").unwrap();
    //     if re.is_match("SS") {
    //         assert!(!literal_const_size("ß", true));
    //     }

    //     // Another tricky example, Armenian ECH YIWN
    //     let re = regex::Regex::new("(?i:\\x{0587})").unwrap();
    //     if re.is_match("\u{0565}\u{0582}") {
    //         assert!(!literal_const_size("\u{0587}", true));
    //     }
    // }

    #[test]
    fn invalid_backref_zero() {
        let tree = Expr::parse_tree(r".\0").unwrap();
        let result = analyze(&tree, 1);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(0)))
        ));

        let result = analyze(&tree, 0);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(0)))
        ));

        let tree = Expr::parse_tree(r"(.)\0").unwrap();
        let result = analyze(&tree, 1);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(0)))
        ));

        let result = analyze(&tree, 0);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(0)))
        ));

        let tree = Expr::parse_tree(r"(.)\0\1").unwrap();
        let result = analyze(&tree, 1);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(0)))
        ));
    }

    #[test]
    fn invalid_backref_no_captures() {
        let tree = Expr::parse_tree(r"aa\1").unwrap();
        let result = analyze(&tree, 1);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(1)))
        ));

        let tree = Expr::parse_tree(r"aaaa\2").unwrap();
        let result = analyze(&tree, 1);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(2)))
        ));
    }

    #[test]
    fn invalid_backref_with_captures() {
        let tree = Expr::parse_tree(r"a(a)\2").unwrap();
        let result = analyze(&tree, 1);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(2)))
        ));

        let tree = Expr::parse_tree(r"a(a)\2\1").unwrap();
        let result = analyze(&tree, 1);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(2)))
        ));
    }

    #[test]
    fn invalid_backref_with_captures_explict_capture_group_zero() {
        let tree = Expr::parse_tree(r"(a(b)\2)c").unwrap();
        let result = analyze(&tree, 0);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(2)))
        ));

        let tree = Expr::parse_tree(r"(a(b)\1\2)c").unwrap();
        let result = analyze(&tree, 0);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(2)))
        ));

        let tree = Expr::parse_tree(r"(a\1)b").unwrap();
        let result = analyze(&tree, 0);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(1)))
        ));

        let tree = Expr::parse_tree(r"(a(b))\2").unwrap();
        let result = analyze(&tree, 0);
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::InvalidBackref(2)))
        ));
    }

    #[test]
    fn allow_analysis_of_self_backref() {
        // even if it will never match, see issue 103
        assert!(!analyze(&Expr::parse_tree(r"(.\1)").unwrap(), 1).is_err());
        assert!(!analyze(&Expr::parse_tree(r"((.\1))").unwrap(), 0).is_err());
        assert!(!analyze(&Expr::parse_tree(r"(([ab]+)\1b)").unwrap(), 1).is_err());
        // in the following scenario it can match
        assert!(!analyze(&Expr::parse_tree(r"(([ab]+?)(?(1)\1| )c)+").unwrap(), 1).is_err());
    }

    #[test]
    fn allow_backref_even_when_capture_group_occurs_after_backref() {
        assert!(!analyze(&Expr::parse_tree(r"\1(.)").unwrap(), 1).is_err());
        assert!(!analyze(&Expr::parse_tree(r"(\1(.))").unwrap(), 0).is_err());
    }

    #[test]
    fn valid_backref_occurs_after_capture_group() {
        assert!(!analyze(&Expr::parse_tree(r"(.)\1").unwrap(), 1).is_err());
        assert!(!analyze(&Expr::parse_tree(r"((.)\1)").unwrap(), 0).is_err());

        assert!(!analyze(&Expr::parse_tree(r"((.)\2\2)\1").unwrap(), 1).is_err());
        assert!(!analyze(&Expr::parse_tree(r"(.)\1(.)\2").unwrap(), 1).is_err());
        assert!(!analyze(&Expr::parse_tree(r"(.)foo(.)\2").unwrap(), 1).is_err());
        assert!(!analyze(&Expr::parse_tree(r"(.)(foo)(.)\3\2\1").unwrap(), 1).is_err());
        assert!(!analyze(&Expr::parse_tree(r"(.)(foo)(.)\3\1").unwrap(), 1).is_err());
        assert!(!analyze(&Expr::parse_tree(r"(.)(foo)(.)\2\1").unwrap(), 1).is_err());
    }

    #[test]
    fn feature_not_yet_supported() {
        let tree = &Expr::parse_tree(r"(a)\g<1>").unwrap();
        let result = analyze(tree, 1);
        assert!(result.is_err());
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::FeatureNotYetSupported(_)))
        ));

        let tree = &Expr::parse_tree(r"(a)\k<1-0>").unwrap();
        let result = analyze(tree, 1);
        assert!(result.is_err());
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::FeatureNotYetSupported(_)))
        ));
    }

    #[test]
    fn subroutine_call_undefined() {
        let tree = &Expr::parse_tree(r"\g<wrong_name>(?<different_name>a)").unwrap();
        let result = analyze(tree, 1);
        assert!(result.is_err());
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(
                CompileError::SubroutineCallTargetNotFound(_, _)
            ))
        ));
    }

    #[test]
    fn left_recursive_subroutine_call() {
        let tree = Expr::parse_tree(r"(?<a>\g<a>)").unwrap();
        let result = analyze(&tree, 1).err();
        println!("{:?}", result);
        assert!(matches!(result, Some(Error::CompileError(CompileError::LeftRecursiveSubroutineCall(1)))));

        let tree = Expr::parse_tree(r"(?<a>(?:\g<a>|))").unwrap();
        let result = analyze(&tree, 1).err();
        println!("{:?}", result);
        assert!(matches!(result, Some(Error::CompileError(CompileError::LeftRecursiveSubroutineCall(1)))));

        let tree = Expr::parse_tree(r"(?<name>a|\g<name>b)").unwrap();
        let result = analyze(&tree, 1).err();
        println!("{:?}", result);
        assert!(matches!(result, Some(Error::CompileError(CompileError::LeftRecursiveSubroutineCall(1)))));
    }

    #[test]
    fn indirect_left_recursive_subroutine_call() {
        let tree = Expr::parse_tree(r"(?<a>(?=\g<b>|))(?<b>\g<a>)").unwrap();
        let result = analyze(&tree, 1).err();
        println!("{:?}", result);
        assert!(matches!(result, Some(Error::CompileError(CompileError::LeftRecursiveSubroutineCall(1)))));
    }

    #[test]
    fn recursive_subroutine_call_not_yet_supported() {
        let tree = Expr::parse_tree(r"(a\g<1>)").unwrap();
        let result = analyze(&tree, 1).err();
        println!("{:?}", result);
        //let expected = "Recursive Subroutine Call".to_string();
        assert!(matches!(
            result,
            Some(Error::CompileError(CompileError::FeatureNotYetSupported(_)))
        ));
    }

    #[test]
    fn less_obvious_recursive_subroutine_call_not_yet_supported() {
        let tree = Expr::parse_tree(r"(?<a>a\g<b>)(?<b>b\g<a>?)").unwrap();
        let result = analyze(&tree, 1);
        println!("{:?}", result);
        //let expected = "Recursive Subroutine Call".to_string();
        assert!(matches!(
            result.err(),
            Some(Error::CompileError(CompileError::FeatureNotYetSupported(_)))
        ));
    }

    #[test]
    fn is_literal() {
        let tree = Expr::parse_tree("abc").unwrap();
        let info = analyze(&tree, 1).unwrap();
        assert_eq!(info.is_literal(), true);
    }

    #[test]
    fn is_literal_with_repeat() {
        let tree = Expr::parse_tree("abc*").unwrap();
        let info = analyze(&tree, 1).unwrap();
        assert_eq!(info.is_literal(), false);
    }

    #[test]
    fn anchored_for_starttext_assertions() {
        let tree = Expr::parse_tree(r"^(\w+)\1").unwrap();
        assert_eq!(can_compile_as_anchored(&tree.expr), true);

        let tree = Expr::parse_tree(r"^").unwrap();
        assert_eq!(can_compile_as_anchored(&tree.expr), true);
    }

    #[test]
    fn not_anchored_for_startline_assertions() {
        let tree = Expr::parse_tree(r"(?m)^(\w+)\1").unwrap();
        assert_eq!(can_compile_as_anchored(&tree.expr), false);
    }
}

/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#[cfg(feature= "expr-cse")]

 use crate::{ast::*, parser::Loc};
 use serde::{Deserialize, Serialize};
 use smol_str::SmolStr;
 use std::{
     collections::{BTreeMap, HashMap, VecDeque},
     hash::Hash,
     sync::Arc,
 };

 
#[derive(Deserialize, Serialize, Hash, Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
/// Flat variable used during the CSE routine
/// distinct from ExprKind::Var
pub struct ExprFlatVar(String);

/// Return a flat variable using the size
/// variable x as part of it's name
fn new_flat_var(counter: &mut usize) -> ExprFlatVar {
    *counter = *counter + 1;
    ExprFlatVar(format!("x{counter}"))
}

#[derive(Deserialize, Serialize, Hash, Debug, Clone, PartialEq, Eq)]
/// Common subexpression elimination
/// form of an expression
/// Currently does not consider the source_loc
pub struct ExprCSE {
    root: ExprKindFlat,
    // ExprKindCSEAtom is only of type ExprCSEVar
    expr_kinds: Vec<(ExprFlatVar,ExprKindFlat)>,
 }

#[derive(Serialize, Deserialize, Hash, Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
 /// Non-recursive expression types
pub enum ExprKindCSEAtom {
    FlatVar(ExprFlatVar),
    Lit(Literal),
    Var(Var),
    Slot(SlotId),
    Unknown(Unknown),
 }

impl From<&ExprFlatVar> for ExprKindCSEAtom {
    fn from(v: &ExprFlatVar) -> Self {
        Self::FlatVar(v.clone())
    }
}

fn expr_kind_cse_atom_to_expr<T: Default + std::clone::Clone>(e: &ExprKindCSEAtom, mapping: &HashMap<&ExprFlatVar, Expr<T>>) -> Result<Expr<T>, &'static str> {
    match e {
        ExprKindCSEAtom::FlatVar(v) => mapping.get(v).ok_or("Mapping not found").cloned(),
        ExprKindCSEAtom::Lit(l) => Ok(ExprBuilder::<T>::new().val(l.clone())),
        ExprKindCSEAtom::Var(v) => Ok(ExprBuilder::<T>::new().var(v.clone())),
        ExprKindCSEAtom::Slot(s) => Ok(ExprBuilder::<T>::new().slot(s.clone())),
        ExprKindCSEAtom::Unknown(u) => Ok(ExprBuilder::<T>::new().unknown(u.clone()))   
    }
}

impl<T: Default + std::clone::Clone> TryFrom<&ExprKindCSEAtom> for Expr<T> {
    type Error = &'static str;

    fn try_from(e: &ExprKindCSEAtom) -> Result<Self, Self::Error> {
        let mapping: HashMap<&ExprFlatVar, Expr<T>> = HashMap::new();
        expr_kind_cse_atom_to_expr(e, &mapping)
    }
}


fn expr_to_atom<T: Default + std::clone::Clone>(e: &Expr<T>, counter: &mut usize) -> ExprKindCSEAtom {
    match e.expr_kind() {
        ExprKind::Lit(l) => ExprKindCSEAtom::Lit(l.clone()),
        ExprKind::Var(v) => ExprKindCSEAtom::Var(v.clone()),
        ExprKind::Slot(s) => ExprKindCSEAtom::Slot(s.clone()),
        ExprKind::Unknown(u) => ExprKindCSEAtom::Unknown(u.clone()),
        _ => ExprKindCSEAtom::FlatVar(new_flat_var(counter))
    }
}
 
#[derive(Serialize, Deserialize, Hash, Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
/// Flattened representation of an expression, refers to
/// ExprFlatVars for subexpressions
pub enum ExprKindFlat {
     Atom(ExprKindCSEAtom),
     If {
         test_expr: ExprKindCSEAtom,
         then_expr: ExprKindCSEAtom,
         else_expr: ExprKindCSEAtom,
     },
     And {
         left: ExprKindCSEAtom,
         right: ExprKindCSEAtom,
     },
     Or {
         left: ExprKindCSEAtom,
         right: ExprKindCSEAtom,
     },
     UnaryApp {
         op: UnaryOp,
         arg: ExprKindCSEAtom,
     },
     BinaryApp {
         op: BinaryOp,
         arg1: ExprKindCSEAtom,
         arg2: ExprKindCSEAtom,
     },
     ExtensionFunctionApp {
         fn_name: Name,
         args: Vec<ExprKindCSEAtom>,
     },
     GetAttr {
         expr: ExprKindCSEAtom,
         attr: SmolStr,
     },
     HasAttr {
         expr: ExprKindCSEAtom,
         attr: SmolStr,
     },
     Like {
         expr: ExprKindCSEAtom,
         pattern: Pattern,
     },
     Is {
         expr: ExprKindCSEAtom,
         entity_type: EntityType,
     },
     Set(Vec<ExprKindCSEAtom>),
     Record(BTreeMap<SmolStr, ExprKindCSEAtom>),
}


fn convert_expr_kind_flat_expr_to_expr<T: Default + std::clone::Clone>(e: &ExprKindFlat, mapping: &HashMap<&ExprFlatVar, Expr<T>>) -> Result<Expr<T>, &'static str> {
    let result = match e {
        ExprKindFlat::Atom(a) => expr_kind_cse_atom_to_expr(a, mapping)?,
        ExprKindFlat::If {test_expr, then_expr, else_expr} => {
            let e1 = expr_kind_cse_atom_to_expr(test_expr, mapping)?;
            let e2 = expr_kind_cse_atom_to_expr(then_expr, mapping)?;
            let e3 = expr_kind_cse_atom_to_expr(else_expr, mapping)?;
            ExprBuilder::<T>::new().ite(e1, e2, e3)
        },
        ExprKindFlat::And {left, right} => {
            let e1 = expr_kind_cse_atom_to_expr(left, mapping)?;
            let e2 = expr_kind_cse_atom_to_expr(right, mapping)?;
            ExprBuilder::<T>::new().and(e1, e2)
        },
        ExprKindFlat::Or {left, right} => {
            let e1 = expr_kind_cse_atom_to_expr(left, mapping)?;
            let e2 = expr_kind_cse_atom_to_expr(right, mapping)?;
            ExprBuilder::<T>::new().or(e1, e2)
        },
        ExprKindFlat::UnaryApp {op, arg} => {
            let e = expr_kind_cse_atom_to_expr(arg, mapping)?;
            ExprBuilder::<T>::new().unary_app(op.clone(), e)
        },
        ExprKindFlat::BinaryApp {op, arg1, arg2} => {
            let e1 = expr_kind_cse_atom_to_expr(arg1, mapping)?;
            let e2 = expr_kind_cse_atom_to_expr(arg2, mapping)?;
            ExprBuilder::<T>::new().binary_app(op.clone(), e1, e2)
        },
        ExprKindFlat::ExtensionFunctionApp {fn_name, args} => {
            let mut es: Vec<Expr<T>> = Vec::with_capacity(args.len());
            for arg in args {
                es.push(expr_kind_cse_atom_to_expr(arg, mapping)?);
            }
            ExprBuilder::<T>::new().call_extension_fn(fn_name.clone(), es)
        },
        ExprKindFlat::GetAttr {expr, attr} => {
            let e = expr_kind_cse_atom_to_expr(expr, mapping)?;
            ExprBuilder::<T>::new().get_attr(e, attr.clone())
        },
        ExprKindFlat::HasAttr {expr, attr} => {
            let e = expr_kind_cse_atom_to_expr(expr, mapping)?;
            ExprBuilder::<T>::new().has_attr(e, attr.clone())
        },
        ExprKindFlat::Like { expr, pattern} => {
            let e = expr_kind_cse_atom_to_expr(expr, mapping)?;
            ExprBuilder::<T>::new().like(e, pattern.iter().cloned())
        },
        ExprKindFlat::Is {expr, entity_type } => {
            let e = expr_kind_cse_atom_to_expr(expr, mapping)?;
            ExprBuilder::<T>::new().is_entity_type(e, entity_type.clone())
        },
        ExprKindFlat::Set(args) => {
            let mut es: Vec<Expr<T>> = Vec::with_capacity(args.len());
            for arg in args {
                es.push(expr_kind_cse_atom_to_expr(arg, mapping)?);
            }
            ExprBuilder::<T>::new().set(es.into_iter())
        },
        ExprKindFlat::Record(records) => {
            let mut rs: BTreeMap<SmolStr, Expr<T>> = BTreeMap::new();
            for (key, value) in records {
                rs.insert(key.clone(), expr_kind_cse_atom_to_expr(value, mapping)?);
            }
            ExprBuilder::<T>::new().record(rs).map_err(|_| "Error creating record")?
        },
    };

    Ok(result)
}

impl<T: Default + std::clone::Clone> TryFrom<&ExprKindFlat> for Expr<T> {
    type Error = &'static str;

    fn try_from(e: &ExprKindFlat) -> Result<Self, Self::Error> {
        let mapping: HashMap<&ExprFlatVar, Expr<T>> = HashMap::new();
        convert_expr_kind_flat_expr_to_expr(e, &mapping)
    }
}

impl ExprKindFlat {
    /// Grab all the atoms from a flat expression
    pub fn atoms_mut<'a>(&'a mut self) -> Vec<&mut ExprKindCSEAtom> {
        let mut subexpr: Vec<&mut ExprKindCSEAtom> = Vec::new();

        match self {
            ExprKindFlat::Atom(a) => { subexpr.push(a); },
            ExprKindFlat::If {test_expr, then_expr, else_expr} => {
                subexpr.push(test_expr);
                subexpr.push(then_expr);
                subexpr.push(else_expr);

            },
            ExprKindFlat::And {left, right} => {
                subexpr.push(left);
                subexpr.push(right);
            },
            ExprKindFlat::Or {left, right} => {
                subexpr.push(left);
                subexpr.push(right);
            },
            ExprKindFlat::UnaryApp {op: _, arg} => {
                subexpr.push(arg);
            },
            ExprKindFlat::BinaryApp {op: _, arg1, arg2} => {
                subexpr.push(arg1);
                subexpr.push(arg2);
            },
            ExprKindFlat::ExtensionFunctionApp {fn_name: _, args} => {
                for arg in args {
                    subexpr.push(arg);
                }
            },
            ExprKindFlat::GetAttr {expr, attr: _} => {
                subexpr.push(expr);
            },
            ExprKindFlat::HasAttr {expr, attr: _} => {
                subexpr.push(expr);
            },
            ExprKindFlat::Like { expr, pattern: _} => {
                subexpr.push(expr);
            },
            ExprKindFlat::Is {expr, entity_type: _} => {
                subexpr.push(expr);
            },
            ExprKindFlat::Set(args) => {
                for arg in args {
                    subexpr.push(arg);
                }
            },
            ExprKindFlat::Record(records) => {
                for arg in records.values_mut() {
                    subexpr.push(arg);
                }
            },
        };

        subexpr
    }

    pub fn atoms<'a>(&'a self) -> Vec<&ExprKindCSEAtom> {
        let mut subexpr: Vec<&ExprKindCSEAtom> = Vec::new();

        match self {
            ExprKindFlat::Atom(a) => { subexpr.push(a); },
            ExprKindFlat::If {test_expr, then_expr, else_expr} => {
                subexpr.push(test_expr);
                subexpr.push(then_expr);
                subexpr.push(else_expr);

            },
            ExprKindFlat::And {left, right} => {
                subexpr.push(left);
                subexpr.push(right);
            },
            ExprKindFlat::Or {left, right} => {
                subexpr.push(left);
                subexpr.push(right);
            },
            ExprKindFlat::UnaryApp {op: _, arg} => {
                subexpr.push(arg);
            },
            ExprKindFlat::BinaryApp {op: _, arg1, arg2} => {
                subexpr.push(arg1);
                subexpr.push(arg2);
            },
            ExprKindFlat::ExtensionFunctionApp {fn_name: _, args} => {
                for arg in args {
                    subexpr.push(arg);
                }
            },
            ExprKindFlat::GetAttr {expr, attr: _} => {
                subexpr.push(expr);
            },
            ExprKindFlat::HasAttr {expr, attr: _} => {
                subexpr.push(expr);
            },
            ExprKindFlat::Like { expr, pattern: _} => {
                subexpr.push(expr);
            },
            ExprKindFlat::Is {expr, entity_type: _} => {
                subexpr.push(expr);
            },
            ExprKindFlat::Set(args) => {
                for arg in args {
                    subexpr.push(arg);
                }
            },
            ExprKindFlat::Record(records) => {
                for arg in records.values() {
                    subexpr.push(arg);
                }
            },
        };

        subexpr
    }

    pub fn vars_mut<'a>(&'a mut self) -> Vec<&mut ExprFlatVar> {
        let mut vars: Vec<&mut ExprFlatVar> = Vec::new();
        for atom in self.atoms_mut() {
            if let ExprKindCSEAtom::FlatVar(v) = atom {
                vars.push(v);
            }
        }
        vars
    }

    pub fn vars<'a>(&'a self) -> Vec<&ExprFlatVar> {
        let mut vars: Vec<&ExprFlatVar> = Vec::new();
        for atom in self.atoms() {
            if let ExprKindCSEAtom::FlatVar(v) = atom {
                vars.push(v);
            }
        }
        vars
    }

}

/// Pushes to the queue if the subexpression isn't flat.
fn push_to_queue_if_flatvar<T: Default + std::clone::Clone>(e: Arc<Expr<T>>, atom: &ExprKindCSEAtom, queue: &mut VecDeque<(ExprFlatVar, Arc<Expr<T>>)>) {
    if let ExprKindCSEAtom::FlatVar(v) = atom {
        queue.push_back((v.clone(), e));
    }
}

/// Return the flattened representation of e, and add to queue any subexpressions that need to be flattened
fn flatten_one_step<T: Default + std::clone::Clone>(e: &Expr<T>, counter: &mut usize, queue: &mut VecDeque<(ExprFlatVar, Arc<Expr<T>>)>) -> ExprKindFlat {
    match e.expr_kind() {
        ExprKind::Lit(l) => ExprKindFlat::Atom(ExprKindCSEAtom::Lit(l.clone())),
        ExprKind::Var(v) => ExprKindFlat::Atom(ExprKindCSEAtom::Var(v.clone())),
        ExprKind::Slot(s) => ExprKindFlat::Atom(ExprKindCSEAtom::Slot(s.clone())),
        ExprKind::Unknown(u) => ExprKindFlat::Atom(ExprKindCSEAtom::Unknown(u.clone())),
        ExprKind::If{ test_expr, then_expr, else_expr } => {
            let x1_name = expr_to_atom(test_expr, counter);
            push_to_queue_if_flatvar(test_expr.clone(), &x1_name, queue);

            let x2_name = expr_to_atom(then_expr, counter);
            push_to_queue_if_flatvar(then_expr.clone(), &x2_name, queue);

            let x3_name = expr_to_atom(else_expr, counter);
            push_to_queue_if_flatvar(else_expr.clone(), &x3_name, queue);

            ExprKindFlat::If { test_expr: x1_name, then_expr: x2_name, else_expr: x3_name }
        },
        ExprKind::And{ left, right} => {
            let x1_name = expr_to_atom(left, counter);
            push_to_queue_if_flatvar(left.clone(), &x1_name, queue);

            let x2_name = expr_to_atom(right, counter);
            push_to_queue_if_flatvar(right.clone(), &x2_name, queue);

            ExprKindFlat::And { left: x1_name, right: x2_name }
        },
        ExprKind::Or{ left, right } => {
            let x1_name = expr_to_atom(left, counter);
            push_to_queue_if_flatvar(left.clone(), &x1_name, queue);

            let x2_name = expr_to_atom(right, counter);
            push_to_queue_if_flatvar(right.clone(), &x2_name, queue);

            ExprKindFlat::Or { left: x1_name, right: x2_name }
        },
        ExprKind::UnaryApp { op, arg } => {
            let x_name = expr_to_atom(arg, counter);
            push_to_queue_if_flatvar(arg.clone(), &x_name, queue);

            ExprKindFlat::UnaryApp { op: op.clone(), arg: x_name }
        },
        ExprKind::BinaryApp { op, arg1, arg2 } => {
            let x1_name = expr_to_atom(arg1, counter);
            push_to_queue_if_flatvar(arg1.clone(), &x1_name, queue);

            let x2_name = expr_to_atom(arg2, counter);
            push_to_queue_if_flatvar(arg2.clone(), &x2_name, queue);

            ExprKindFlat::BinaryApp { op: op.clone(), arg1: x1_name, arg2: x2_name }
        }
        ExprKind::ExtensionFunctionApp { fn_name, args} => {
            let mut pargs: Vec<ExprKindCSEAtom> = Vec::new();
            for arg in args.as_ref() {
                let x_name = expr_to_atom(arg, counter);
                pargs.push(x_name.clone());
                let aarg = Arc::new(arg.clone());
                push_to_queue_if_flatvar(aarg, &x_name, queue);
            }

            ExprKindFlat::ExtensionFunctionApp { fn_name: fn_name.clone(), args: pargs }
        },
        ExprKind::GetAttr{ expr, attr } => {
            let x_name = expr_to_atom(expr, counter);
            push_to_queue_if_flatvar(expr.clone(), &x_name, queue);
            ExprKindFlat::GetAttr { expr: x_name, attr: attr.clone() }
        },
        ExprKind::HasAttr { expr, attr } => {
            let x_name = expr_to_atom(expr, counter);
            push_to_queue_if_flatvar(expr.clone(), &x_name, queue);
            ExprKindFlat::HasAttr { expr: x_name, attr: attr.clone()}
        },
        ExprKind::Like { expr, pattern } => {
            let x_name = expr_to_atom(expr, counter);
            push_to_queue_if_flatvar(expr.clone(), &x_name, queue);
            ExprKindFlat::Like { expr: x_name, pattern: pattern.clone()}
        },
        ExprKind::Is { expr, entity_type } => {
            let x_name = expr_to_atom(expr, counter);
            push_to_queue_if_flatvar(expr.clone(), &x_name, queue);
            ExprKindFlat::Is { expr: x_name, entity_type: entity_type.clone()}
        },
        ExprKind::Set(exprs) => {
            let mut pargs: Vec<ExprKindCSEAtom> = Vec::new();
            for arg in exprs.as_ref() {
                let x_name = expr_to_atom(&Arc::new(arg), counter);
                pargs.push(x_name.clone());
                let aarg = Arc::new(arg.clone());
                push_to_queue_if_flatvar(aarg, &x_name, queue);
            }

            ExprKindFlat::Set(pargs)
        },
        ExprKind::Record(recs) => {
            let mut precs: BTreeMap<SmolStr, ExprKindCSEAtom> = BTreeMap::new();
            for (key, value) in recs.as_ref() {
                let x_name = expr_to_atom(&Arc::new(value), counter);
                let aarg = Arc::new(value.clone());
                push_to_queue_if_flatvar(aarg, &x_name, queue);
                precs.insert(key.clone(), x_name);
            }

            ExprKindFlat::Record(precs)
        },
    }
}

fn find_matching_subexpressions<'a>(exprs: &'a Vec<(ExprFlatVar, ExprKindFlat)>) -> Option<((usize, &ExprFlatVar), (usize, &ExprFlatVar))> {
    let mut matching_subexpressions: Option<((usize, &ExprFlatVar), (usize, &ExprFlatVar))> = None;

    if exprs.len() == 0 {
        return matching_subexpressions
    }

    for i in 0..(exprs.len() - 1) {
        for j in (i + 1)..exprs.len() {
            let (var_i, subexpr_i) = &exprs[i];
            let (var_j, subexpr_j) = &exprs[j];

            if subexpr_i == subexpr_j {
                matching_subexpressions = Some(((i, var_i), (j, var_j)));
                break;
            }
        }
    }

    matching_subexpressions
}

/// Replace every instance of x with y within exprs.
fn flat_vec_variable_renaming(exprs: &mut Vec<(ExprFlatVar, ExprKindFlat)>, x: &ExprFlatVar, y: &ExprFlatVar) {
    for (_, subexpr) in exprs {
        flat_variable_renaming(subexpr, x, y);
    }
}

fn flat_variable_renaming(expr: &mut ExprKindFlat, x: &ExprFlatVar, y: &ExprFlatVar) {
    for atom in expr.atoms_mut() {
        if let ExprKindCSEAtom::FlatVar(v) = atom {
            if x == v {
                *atom = ExprKindCSEAtom::FlatVar(y.clone())
            }
        }
    }
}

/// Takes an expression, flattens it, performs common
/// subexpression elimination, and returns the result
/// as a ExprCSE type.
pub fn convert_expr_to_expr_cse<T: Default + std::clone::Clone>(e: &Expr<T>) -> ExprCSE {
    let mut processed: Vec<(ExprFlatVar, ExprKindFlat)> = Vec::new();
    let mut queue: VecDeque<(ExprFlatVar, Arc<Expr<T>>)> = VecDeque::new();
    let mut counter: usize = 0;

    // let root = ExprKindFlat::Atom(ExprKindCSEAtom::Lit(Literal::String("hello".into())));

    let mut root = flatten_one_step(e, &mut counter, &mut queue);

    // Flatten until there are no more subexpressions to flatten
    while !queue.is_empty() {
        let (ei_name, ei) = queue.pop_front().unwrap();
        let flattened_term = flatten_one_step(ei.as_ref(), &mut counter, &mut queue);
        processed.push((ei_name, flattened_term));
    }

    // Perform common subexpression elimination
    while let Some(((i, var_i), (j, var_j))) = find_matching_subexpressions(&processed) {
        // We're going to delete the larger index
        let (max_index, _, var_max, var_min) = if i >= j {
            (i, j, var_i, var_j)
        } else {
            (j, i, var_j, var_i)
        };
        let var_max = var_max.clone();
        let var_min = var_min.clone();
        processed.swap_remove(max_index); // O(1) removal

        // Replace every instance of var_max with var_min
        flat_vec_variable_renaming(&mut processed, &var_max, &var_min);
        flat_variable_renaming(&mut root, &var_max, &var_min);
    }

    ExprCSE {
        root: root,
        expr_kinds: processed,
    }
}

impl From<&Expr> for ExprCSE {
    fn from(e: &Expr) -> Self {
        convert_expr_to_expr_cse(e)
    } 
}

impl<T: Default + std::clone::Clone> From<Expr<T>> for ExprCSE {
    fn from(e: Expr<T>) -> Self {
        let x = convert_expr_to_expr_cse(&e);
        println!("{}", x.expr_kinds.len());
        x
        // Self {
        //     root: ExprKindFlat::Atom(ExprKindCSEAtom::Lit(Literal::String("hello".into()))),
        //     expr_kinds: Vec::new()
        // }
    } 
}


/// Takes an ExprCSE and tries to unfold it to an Expr
/// type. May fail.
// Fixme: Figure out a way to make this an immutable reference
pub fn convert_expr_cse_to_expr<T: Default + std::clone::Clone>(e: &ExprCSE) -> Result<Expr<T>, &'static str> {

    // These subexpressions have no dependencies
    let (flat_leaves, mut flat_remaining): (Vec<_>, Vec<_>) = e.expr_kinds
        .iter()
        .partition(|(_, term)| term.vars().len() == 0);

    let mut processed_subexpressions: HashMap<&ExprFlatVar, Expr<T>> = flat_leaves
        .iter()
        .map(|(v, term)| {
            (v, Expr::<T>::try_from(term).expect("Leaves failed...")) // Figure out how to remove .expect
        })
        .collect();

    while flat_remaining.len() > 0 {
        let mut substitution_performed: bool = false;
        flat_remaining.retain(|(flat_var, expr_flat)| {
            let result = convert_expr_kind_flat_expr_to_expr(expr_flat, &processed_subexpressions);
            match result {
                Ok(expr) => {
                    substitution_performed = true;
                    processed_subexpressions.insert(flat_var, expr);
                    false // Don't retain as it's now processed
                }
                Err(_) => true
            }
        });
        if !substitution_performed {
            panic!("Expected to perform a substitution");
        }
    }

    convert_expr_kind_flat_expr_to_expr(&e.root, &processed_subexpressions)
}

impl<T: Default + std::clone::Clone> TryFrom<&ExprCSE> for Expr<T> {
    type Error = &'static str;
    fn try_from(e: &ExprCSE) -> Result<Self, Self::Error> {
        convert_expr_cse_to_expr(e)
    }
}

impl<T: Default + std::clone::Clone> TryFrom<ExprCSE> for Expr<T> {
    type Error = &'static str;
    fn try_from(e: ExprCSE) -> Result<Self, Self::Error> {
        convert_expr_cse_to_expr(&e)
    }
}


#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    pub fn visual_check() {
        // let x = Expr::and(Expr::and(Expr::val("A"), Expr::and(Expr::val("B"), Expr::val("C"))), Expr::and(Expr::val("B"), Expr::val("C")));
        let a = Expr::val("A");
        let b = Expr::val("B");
        let c = Expr::val("C");
        let x = Expr::and(
            Expr::and(
                Expr::and(
                    a.clone(),
                    Expr::and(b.clone(), c.clone())
                ),
                a.clone()
            ),
            Expr::and(
                Expr::and(b.clone(), c.clone()),
                Expr::and(
                    a.clone(),
                    Expr::and(b.clone(), c.clone())
                )
            )
        );

        let x2  = ExprCSE::from(&x);

        let x3 = Expr::<()>::try_from(&x2).unwrap();

        // let x2 = convert_expr_to_expr_cse(&x);


        // let x3 = convert_expr_cse_to_expr(&x2).unwrap();

        println!("{x}");
        println!("{:?}", x2);
        println!("{x3}");
    }

}



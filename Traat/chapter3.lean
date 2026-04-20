import Traat.chapter2

section Unification

open Term Subst

def Unifier (σ : Subst) (t u : Term) : Prop := t.apply σ = u.apply σ

def Unify (t u : Term) : Prop := ∃ σ, Unifier σ t u

def varSubst (x : Var) (t : Term) : Subst := fun y => if y = x then t else var y

@[simp]
lemma varSubst_of_ne (h : y ≠ x) : varSubst x t y = var y := by grind [varSubst]

@[simp]
lemma varSubst_self : varSubst x t x = t := by grind [varSubst]

@[grind →]
lemma Unifier.symm (σ : Subst) (t u : Term) (_ : Unifier σ t u) : Unifier σ u t := by
  simp only [Unifier] at *; grind

def varUnify (x : Var) (t : Term) : Option Subst :=
  if (x ∈ t.vars ∧ t ≠ var x) then none
  else varSubst x t

@[grind =]
lemma varUnify_some_iff (x : Var) (t : Term) :
  (varUnify x t).isSome ↔ (x ∉ t.vars ∨ t = var x) := by grind [varUnify]

@[grind .]
lemma vars_app_left_subset (t₁ t₂ : Term) : t₁.vars ⊆ (t₁ @@ t₂).vars := by
  simp only [vars, Finset.subset_union_left]

@[grind .]
lemma vars_app_right_subset (t₁ t₂ : Term) : t₂.vars ⊆ (t₁ @@ t₂).vars := by
  simp only [vars, Finset.subset_union_right]

lemma Term.apply_congr_vars (t : Term) (σ τ : Subst) (h : ∀ x ∈ t.vars, σ x = τ x) : t.apply σ = t.apply τ := by
  induction t <;> simp [Term.apply, Term.vars] at * <;> grind only

lemma Term.apply_eq_of_disjoint_dom (t : Term) (σ : Subst) (h : Disjoint σ.dom t.vars) : t.apply σ = t := by
  have h' : t = t.apply idSubst := by grind
  have h'' : ∀ x ∈ t.vars, σ x = idSubst x := by
    intros x; simp [idSubst]
    rw [Set.disjoint_right] at h
    simp only [SetLike.mem_coe, dom, ne_eq, Set.mem_setOf_eq, Decidable.not_not] at h
    apply h
  grind [Term.apply_congr_vars]

lemma varSubst_dom_subset (x : Var) (t : Term) :
  (varSubst x t).dom ⊆ {x} := by
  simp [dom, varSubst]

lemma varSubst_dom_eq_of_ne (x : Var) (t : Term) (_ : t ≠ var x) :
  (varSubst x t).dom = {x} := by simp only [dom, varSubst]; grind

lemma varSubst_dom_cases (x : Var) (t : Term) :
  (varSubst x t).dom = {x} ∨ (varSubst x t).dom = {} := by
  have h := varSubst_dom_subset x t
  grind

lemma varUnify_dom_subset (x : Var) (t : Term) (h : varUnify x t |>.isSome) :
  (varUnify x t |>.get h).dom ⊆ {x} := by
  simp only [dom, varUnify, ne_eq, Option.get_ite', varSubst, ite_eq_right_iff, Classical.not_imp,
    Set.subset_singleton_iff, Set.mem_setOf_eq, and_imp, forall_eq, implies_true]

@[simp]
lemma varUnify_self (x : Var) (h : varUnify x (var x) |>.isSome) :
  (varUnify x (var x)).get h = idSubst := by
  funext y
  by_cases h : y = x
  . simp only [varUnify, ne_eq, h, Option.get_ite', varSubst_self,
    idSubst]
  . simp only [varUnify, ne_eq, Option.get_ite', h, not_false_eq_true,
    varSubst_of_ne]

@[simp]
lemma varUnify_get_eq_varSubst (x : Var) (t : Term) (h₁ : varUnify x t |>.isSome) :
  (varUnify x t).get h₁ = varSubst x t := by
  funext; simp only [varUnify, ne_eq, Option.get_ite']

lemma varUnify_unifies (x : Var) (t : Term) (h : varUnify x t |>.isSome) :
  (varUnify x t).get h x = t.apply ((varUnify x t).get h) := by
  have h₁ : x ∉ t.vars ∨ t = var x := by
    simp only [varUnify, ne_eq, Option.isSome_ite', not_and, Decidable.not_not] at h; grind
  cases h₁
  case _ =>
    have h₂ : Disjoint ((varUnify x t).get h).dom t.vars := by
      grind [varUnify_dom_subset]
    rw [Term.apply_eq_of_disjoint_dom]; simp only [varUnify, ne_eq, Option.get_ite', varSubst_self]; trivial
  case _ h =>
    simp only [varUnify, h, ne_eq, not_true_eq_false, and_false, Option.get_ite', varSubst_self,
      ↓reduceIte, Option.get_some, apply]

lemma varUnify_mgu_aux (x : Var) (t : Term) (σ : Subst)
  (hasUnifier : σ x = t.apply σ)
  : ∃ τ : Subst, (varSubst x t).scomp τ = σ := by
  exists (fun y => if y = x then t.apply σ else σ y)
  funext y
  by_cases h:(y = x); simp [h, scomp]
  . rw [Term.apply_congr_vars t _ σ] <;> grind
  . simp only [scomp, ne_eq, h, not_false_eq_true, varSubst_of_ne, apply, ↓reduceIte]

lemma varUnify_mgu (x : Var) (t : Term) (σ : Subst)
  (unifies : varUnify x t |>.isSome)
  (hasUnifier : σ x = t.apply σ)
  : let mgu := varUnify x t |>.get unifies
  ∃ τ : Subst, mgu.scomp τ = σ := by
  simp only [varUnify, ne_eq, Option.get_ite']
  apply varUnify_mgu_aux; trivial

lemma sizeOf_lt_of_mem_vars (x : Var) (t : Term) (σ : Subst) (mem : x ∈ t.vars) (ne : t ≠ var x) :
  sizeOf (σ x) < sizeOf (t.apply σ) := by
  induction t
  case _ => grind only [vars, = Finset.mem_singleton]
  case _ => grind only [vars, ← Finset.notMem_empty]
  case _ t₁ t₂ ih₁ ih₂ =>
    simp only [apply, app.sizeOf_spec]; simp only [vars, Finset.mem_union] at mem
    cases mem
    . by_cases eq:(t₁ = var x)
      . simp only [eq, apply]; grind only
      . grind only
    . by_cases eq:(t₂ = var x)
      . simp only [eq, apply, Nat.lt_add_left_iff_pos]; grind only
      . grind only

lemma varUnify_isSome_of_unifier (x : Var) (t : Term) (σ : Subst)
  (hasUnifier : σ x = t.apply σ) :
  varUnify x t |>.isSome := by
  by_contra
  have h : (varUnify x t) |>.isNone := by revert this; simp only [Bool.not_eq_true,
    Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, imp_self]
  have h' : x ∈ t.vars := by grind only [= varUnify_some_iff]
  have h'' : t ≠ var x := by grind only [= varUnify_some_iff]
  have h₃ := sizeOf_lt_of_mem_vars x t σ (by trivial) (by trivial)
  grind only

instance domDec {σ : Subst} {x : Var} : Decidable (x ∈ σ.dom) :=
  if h : σ x = var x then .isFalse (by simp [dom]; exact h) else .isTrue h

@[simp]
def Subst.join (σ₁ σ₂ : Subst) : Subst :=
  fun x => if x ∈ σ₁.dom then σ₁ x else σ₂ x

lemma Subst.join_comm_of_disjoint (σ₁ σ₂ : Subst) (disj : Disjoint σ₁.dom σ₂.dom) : σ₁.join σ₂ = σ₂.join σ₁ := by
  funext x; simp
  by_cases h : (x ∈ σ₁.dom)
  . simp only [Set.disjoint_left] at *
    grind
  . simp only [h]
    simp only [dom] at *; grind only [usr Set.mem_setOf_eq]

@[simp]
lemma Subst.join_dom (σ₁ σ₂ : Subst) : (σ₁.join σ₂).dom = σ₁.dom ∪ σ₂.dom := by
  simp only [join, dom, setOf, Union.union, Set.union, Membership.mem, Set.Mem]
  funext x; grind

@[simp]
lemma Subst.scomp_dom_subset (σ₁ σ₂ : Subst) : (σ₁.scomp σ₂).dom ⊆ σ₁.dom ∪ σ₂.dom := by
  simp only [dom]; intro x; simp only [scomp, ne_eq, Set.mem_setOf_eq, Set.mem_union]
  rw [← Classical.not_and_iff_not_or_not]
  intros; grind only [apply]

structure UnifyState where
  subst : Subst
  constraints : List (Term × Term)

def constrVars : List (Term × Term) → Finset Var
| [] => {}
| (t, u) :: cs => t.vars ∪ u.vars ∪ (constrVars cs)

def Subst.map₂ (σ : Subst) (l : List (Term × Term)) : List (Term × Term) :=
  l.map (fun (x, y) => (x.apply σ, y.apply σ))

@[simp]
lemma Subst.idSubstDom : idSubst.dom = ∅ := by
  simp only [dom, idSubst, ne_eq, not_true_eq_false, Set.setOf_false]

@[simp]
lemma Subst.map₂_id (l : List (Term × Term)) : idSubst.map₂ l = l := by
  induction l <;> grind [Subst.map₂]

lemma apply_vars_subset (t : Term) (σ : Subst) (codom_inc : ∀ x ∈ t.vars, (σ x).vars ⊆ S) :
  (t.apply σ).vars ⊆ S := by
  induction t <;> simp only [apply, vars, Finset.empty_subset] <;> simp only [vars,
    Finset.mem_singleton, forall_eq] at codom_inc <;> grind only [= Finset.subset_iff,
      = Finset.mem_union]

lemma not_mem_vars_of_codom (t : Term) (σ : Subst) (x : Var) (h : ∀ y, x ∉ (σ y).vars) : x ∉ (t.apply σ).vars := by
  induction t <;> simp [apply, vars] <;> grind

lemma constrVars_apply_subset (l : List (Term × Term)) (σ : Subst)
  (codom_inc : ∀ x ∈ constrVars l, (σ x).vars ⊆ S) :
  constrVars (σ.map₂ l) ⊆ S := by
  revert codom_inc; induction l <;> simp [constrVars, Subst.map₂]
  case _ head tail ih =>
    intros codom_inc
    rw [Finset.union_subset_iff, Finset.union_subset_iff]
    apply And.intro
    . grind only [= Finset.subset_iff, apply_vars_subset]
    . apply And.intro; grind only [= Finset.subset_iff, apply_vars_subset]
      apply ih; grind

lemma not_mem_constrVars_of_codom (l : List (Term × Term)) (σ : Subst) (x : Var)
  (h : ∀ y, x ∉ (σ y).vars)
  : x ∉ constrVars (σ.map₂ l) := by
  induction l <;> simp [Subst.map₂, constrVars]
  case _ t₁ t₂ ih =>
    have h' := fun t => not_mem_vars_of_codom t σ x h
    exact ⟨h' _, h' _, ih⟩ -- why doesn't grind work here?


def unifyStep (st : UnifyState) : Option UnifyState :=
  match st.constraints with
  | [] => none -- kind of a hack to fail here, but we won't hit this branch.
  | (var x, t) :: cstr => do
    let σ ← varUnify x t
    return ⟨st.subst.scomp σ, σ.map₂ cstr⟩
  | (t, var x) :: cstr => do
    return ⟨st.subst, (var x, t)::cstr⟩
  | (func f, func g) :: cstr =>
    if f = g then
      return ⟨st.subst, cstr⟩
    else failure
  | (t₁ @@ u₁, t₂ @@ u₂) :: cstr => do
    return ⟨st.subst, (t₁, t₂) :: (u₁, u₂) :: cstr⟩
  | (_, _) :: _ => failure

noncomputable def constrSize : List (Term × Term) → ℕ
| [] => 0
| (t₁, t₂) :: cstrs => 1 + sizeOf t₁ + sizeOf t₂ + (constrSize cstrs)

def rhsVarSize : List (Term × Term) → ℕ
| [] => 0
| (t₁, t₂) :: cstrs =>
  if ¬ isVar t₁ ∧ isVar t₂
  then 1 + rhsVarSize cstrs
  else rhsVarSize cstrs

noncomputable def ltState (st : UnifyState) : ℕ × ℕ × ℕ :=
  (constrVars st.constraints |> Finset.card,
   constrSize st.constraints,
   rhsVarSize st.constraints)

lemma Finset.card_lt_card_of_le_of_mem_not_mem α (s s' : Finset α) (x : α) :
  s ≤ s' → x ∈ s' → x ∉ s → s.card < s'.card := by
  simp; intros; apply Finset.card_lt_card; grind

@[grind →]
lemma varUnify_isSome_of_unifyStep
  (h : (unifyStep { subst := subst, constraints := (var x, u) :: tail }).isSome) :
  (varUnify x u).isSome := by
  revert h; simp only [unifyStep, Option.pure_def, Option.bind_eq_bind, Option.bind]
  split <;> grind

-- This is the clever bit: we get rid of a variable with that `varUnify`,
-- which decreases the second leg of the measure.
private lemma constrRemoveVar
  (h : (varUnify x u).isSome)
  (h' : u ≠ var x) :
  (constrVars ((varSubst x u).map₂ tail)).card <
  (insert x (u.vars ∪ constrVars tail)).card := by
  apply Finset.card_lt_card_of_le_of_mem_not_mem (x := x)
  . have vu_some : (varUnify x u).isSome := by grind
    have h' := constrVars_apply_subset (S := u.vars ∪ constrVars tail) tail (varSubst x u)
    apply Finset.Subset.trans (s₂ := u.vars ∪ constrVars tail)
    . apply h'
      intros y h
      by_cases eq:(y = x)
      . rw [eq]; simp only [varSubst_self, Finset.subset_union_left]
      . simp only [ne_eq, eq, not_false_eq_true, varSubst_of_ne, vars, Finset.singleton_subset_iff,
        Finset.mem_union]
        grind only
    . simp only [Finset.subset_insert]
  . grind
  . have vu_some : (varUnify x u).isSome := by grind only
    apply not_mem_constrVars_of_codom
    intros y; by_cases h':(y = x)
    . simp only [h', varSubst_self]; grind only [= varUnify_some_iff]
    . simp only [ne_eq, h', not_false_eq_true, varSubst_of_ne, vars, Finset.mem_singleton]; grind only

lemma apply_varSubst_self (t : Term) : t.apply (varSubst x (var x)) = t := by
  induction t <;> simp only [apply, varSubst, ite_eq_right_iff, var.injEq] <;> grind

@[simp]
lemma varSubst_self_eq_idSubst : (varSubst x (var x)) = idSubst := by
  funext; simp only [varSubst, idSubst, ite_eq_right_iff, var.injEq]; grind

@[simp]
lemma Subst.map₂_varSubst_self : (varSubst x (var x)).map₂ l = l := by
  induction l <;> simp only [map₂, varSubst_self_eq_idSubst, idSubst_apply, Prod.mk.eta,
    List.map_cons, List.map_id_fun', id_eq]

-- This is quite a bit more tedious than I'd like.
lemma ltState_decreasing : Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
  (ltState ((unifyStep st).get h)) (ltState st) := by
  have ⟨_, l⟩ := st
  rcases l with _ | ⟨⟨t, u⟩, tail⟩ <;> simp only [unifyStep]
  case nil => simp only [unifyStep, Option.isSome_none, Bool.false_eq_true] at h
  case cons =>
  cases t
  case _ x =>
    by_cases (u = var x)
    case _ h' =>
      apply Prod.Lex.right' <;> simp only [h', Option.pure_def, Option.bind_eq_bind,
        Option.get_bind, varUnify_get_eq_varSubst, varSubst_self_eq_idSubst, scomp_idSubst, map₂_id,
        Option.get_some]
      . simp only [constrVars, Finset.union_idempotent]
        apply Finset.card_mono
        simp only [LE.le, Finset.mem_union]
        grind
      . apply Prod.Lex.left
        simp only [constrSize, var.sizeOf_spec, sizeOf_default, Nat.add_zero, Nat.reduceAdd,
          Nat.lt_add_left_iff_pos, Nat.zero_lt_succ]
    case _ =>
      apply Prod.Lex.left; simp only [Option.pure_def, Option.bind_eq_bind, Option.get_bind,
        varUnify_get_eq_varSubst, Option.get_some, constrVars, vars, Finset.singleton_union,
        Finset.insert_union]
      apply constrRemoveVar <;> grind only [→ varUnify_isSome_of_unifyStep]
  case _ =>
    cases u
    case _ f x =>
      apply Prod.Lex.right; apply Prod.Lex.right; simp only [Option.pure_def, Option.get_some,
        rhsVarSize, isVar, not_true_eq_false, Bool.false_eq_true, and_self, ↓reduceIte,
        not_false_eq_true, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
    case _ =>
      apply Prod.Lex.right' <;> simp only [Option.pure_def, Option.failure_eq_none, Option.get_ite,
        constrVars, Finset.union_assoc]
      . apply Finset.card_mono
        simp only [LE.le, Finset.mem_union]; grind
      . apply Prod.Lex.left
        simp only [constrSize, func.sizeOf_spec, sizeOf_default, Nat.add_zero, Nat.reduceAdd,
          Nat.lt_add_left_iff_pos, Nat.zero_lt_succ]
    case _ => simp only [unifyStep, Option.failure_eq_none, Option.isSome_none,
      Bool.false_eq_true] at h
  case _ t₁ t₂ =>
    cases u
    case _ x =>
      apply Prod.Lex.right'
      . simp only [Option.pure_def, Option.get_some, constrVars, Finset.union_assoc]; grind
      . apply Prod.Lex.right'
        . simp only [Option.pure_def, Option.get_some, constrSize, var.sizeOf_spec, sizeOf_default,
          Nat.add_zero, Nat.reduceAdd, app.sizeOf_spec, Nat.add_le_add_iff_right]; grind
        . simp only [Option.pure_def, Option.get_some, rhsVarSize, isVar, not_true_eq_false,
          Bool.false_eq_true, and_self, ↓reduceIte, not_false_eq_true, Nat.lt_add_left_iff_pos,
          Nat.lt_add_one]
    case _ => simp only [unifyStep, Option.failure_eq_none, Option.isSome_none,
      Bool.false_eq_true] at h
    case _ =>
      apply Prod.Lex.right' <;> simp only [Option.pure_def, Option.get_some, constrVars,
        Finset.union_assoc]
      . apply Finset.card_mono
        simp only [LE.le, Finset.mem_union, vars, Finset.union_assoc]; grind
      . simp only [constrSize, app.sizeOf_spec]; grind

def unify_aux (st : UnifyState) : Option UnifyState :=
  match st.constraints with
  | [] => return st
  | _ =>
    -- We can't use pretty do notation here to not confuse the termination
    -- checker
    let st' := unifyStep st
    if h: st'.isSome then unify_aux (st'.get h) else none
  termination_by ltState st
  decreasing_by
    apply ltState_decreasing

def unify (t u : Term) : Option Subst := unify_aux ⟨idSubst, [(t, u)]⟩ |>.map (fun st => st.subst)

-- This is the "simple" version, but proving termination is quite hard.
partial def unify' (t₁ t₂ : Term) : Option Subst :=
  match t₁, t₂ with
  | func f, func g => if f = g then idSubst else none
  | var x, t => varUnify x t
  | t, var x => varUnify x t
  | t₁ @@ u₁, t₂ @@ u₂ =>
    do
      let σ₁ ← unify' t₁ t₂
      let σ₂ ← unify' (u₁.apply σ₁) (u₂.apply σ₁)
      return σ₁.join σ₂
  | _, _ => none


-- Ok let's start proving that `unify` actually unifies.

def ConstrUnifier (σ : Subst) (l : List (Term × Term)) : Prop :=
  match l with
  | [] => True
  | (t, u) :: l' =>
    Unifier σ t u ∧ ConstrUnifier σ l'

def SubstUnifier (σ τ : Subst) : Prop := ∀ x, σ x = (τ x).apply σ

def StateUnifier (σ : Subst) (st : UnifyState) : Prop :=
  SubstUnifier σ st.subst ∧ ConstrUnifier σ st.constraints

def isUnifyFail (t u : Term) : Bool :=
  match t, u with
  | var _, _
  | _, var _
  | func _, func _
  | _ @@ _, _ @@ _ => false
  | _, _ => true

@[grind =>]
lemma not_unifier_of_isUnifyFail : isUnifyFail t u → ¬ Unifier σ t u := by
  induction t <;> induction u <;> simp [isUnifyFail, Unifier, apply]

-- ugh this is ugly
private lemma unify_induction (P : List (Term × Term) → Prop)
  (l : List (Term × Term))
  (h₀ : ∀ l t u, isUnifyFail t u → P ((t, u)::l))
  (h₁ : P [] )
  (h₂ : ∀ l x t, P l → P ((var x, t)::l))
  (h₃ : ∀ l x t, (∀ y, t ≠ var y) → P l → P ((t, var x)::l))
  (h₄ : ∀ l f g, P l → P ((func f, func g)::l))
  (h₅ : ∀ l t₁ t₂ u₁ u₂, P l → P ((t₁ @@ t₂, u₁ @@ u₂)::l))
  : P l := by
  induction l
  case _ => grind
  case _ p l ih =>
    let (t, u) := p
    cases t <;> cases u <;> try grind
    case _ => apply h₀; eq_refl
    case _ => apply h₀; eq_refl

-- ugh this is ugly also
private lemma unify_induction' (P : Term → Term → Prop)
  (t u : Term)
  (h₀ : ∀ t u, isUnifyFail t u → P t u)
  (h₂ : ∀ x t, P (var x) t)
  (h₃ : ∀ x t, (∀ y, t ≠ var y) → P t (var x))
  (h₄ : ∀ f g, P (func f) (func g))
  (h₅ : ∀ t₁ t₂ u₁ u₂, P t₁ u₁ → P t₂ u₂ → P (t₁ @@ t₂) (u₁ @@ u₂))
  : P t u := by
  revert u; induction t <;> intro u
  case _ => grind
  case _ f =>
    cases u
    case _ => grind
    case _ => grind
    case _ => apply h₀; simp only [isUnifyFail]
  case _ =>
    induction u
    case _ => grind
    case _ => apply h₀; simp only [isUnifyFail]
    case _ => apply h₅ <;> grind

lemma apply_apply_varSubst (σ : Subst) (x : Var) (t : Term) (u : Term)
  (unify : t.apply σ = σ x)
  : (u.apply <| varSubst x t).apply σ = u.apply σ := by
  induction u <;> simp only [apply]
  case var y =>
    by_cases h:(y = x) <;> simp [h, apply]
    . trivial
  case _ => grind only

lemma Unifier.apply_varSubst (σ : Subst) (x : Var) (t : Term) (u₁ u₂ : Term)
  (unify₁ : t.apply σ = σ x)
  (unify₂ : Unifier σ u₁ u₂)
   : Unifier σ (u₁.apply (varSubst x t)) (u₂.apply (varSubst x t)) := by
  simp only [Unifier] at unify₂
  simp only [Unifier]; rw [apply_apply_varSubst] <;> try rw [apply_apply_varSubst] <;> grind
  grind

lemma ConstrUnifier.apply_varSubst (σ : Subst) (x : Var) (t : Term) (l : List (Term × Term))
  (unify₁ : t.apply σ = σ x)
  (unify₂ : ConstrUnifier σ l)
   : ConstrUnifier σ ((varSubst x t).map₂ l) := by
  induction l <;> simp only [map₂, List.map_nil, ConstrUnifier]; simp only [ConstrUnifier] at unify₂
  case _ head tl ih =>
  constructor
  . apply Unifier.apply_varSubst <;> grind
  . apply ih; grind

lemma Unifier.of_apply_varSubst (σ : Subst) (x : Var) (t u₁ u₂ : Term)
  (h₁ : Unifier σ (var x) t)
  (h₂ : Unifier σ (u₁.apply (varSubst x t))
                  (u₂.apply (varSubst x t)))
  : Unifier σ u₁ u₂ := by
  revert h₂; simp only [Unifier]
  rw [apply_apply_varSubst, apply_apply_varSubst]; grind
  . symm; apply h₁
  . symm; apply h₁

lemma ConstrUnifier.of_apply_varSubst (σ : Subst) (x : Var) (t : Term) l
  (h₁ : Unifier σ (var x) t)
  (h₂ : ConstrUnifier σ (varSubst x t |>.map₂ l))
  : ConstrUnifier σ l := by
  revert h₂; induction l <;> simp [ConstrUnifier, Subst.map₂]
  case _ hd tl ih =>
  cases hd
  case _ =>
    simp
    intros _ h; constructor
    . grind only [Unifier.of_apply_varSubst]
    . apply ih; apply h

lemma Subst.scomp_varSubst_of_eq (σ : Subst) x (t : Term)
  (h : σ x = t.apply σ)
  : (varSubst x t).scomp σ = σ := by
  funext y; simp [scomp]
  by_cases h':(y = x) <;> simp [h', apply]; grind

lemma Unifier.scomp_eq_aux (σ τ : Subst)
  : Unifier (τ.scomp σ) u₁ u₂ =
    Unifier σ (u₁.apply τ) (u₂.apply τ) := by
  simp only [Unifier, scomp_apply]

lemma Unifier.eq_apply_varSubst (σ : Subst) x (t : Term)
  (h₁ : σ x = t.apply σ)
  : Unifier σ u₁ u₂ =
    Unifier σ (u₁.apply (varSubst x t)) (u₂.apply (varSubst x t)) := by
  rw [← Unifier.scomp_eq_aux, Subst.scomp_varSubst_of_eq]; trivial

lemma SubstUnifier.eq_scomp_varSubst (σ τ : Subst) x (t : Term)
  (h₁ : σ x = t.apply σ)
  : SubstUnifier σ τ =
    SubstUnifier σ (τ.scomp (varSubst x t)) := by
  simp only [SubstUnifier, eq_iff_iff]
  constructor
  . intros h y
    simp only [scomp]; rw [← scomp_apply, Subst.scomp_varSubst_of_eq]
    . apply h
    . trivial
  . intros h y
    have h := h y
    simp only [scomp] at h
    rw [← scomp_apply, Subst.scomp_varSubst_of_eq] at h
    . apply h
    . trivial

lemma ConstrUnifier.eq_apply_varSubst (σ : Subst) x (t : Term)
  (h₁ : σ x = t.apply σ)
  : ConstrUnifier σ l =
    ConstrUnifier σ ((varSubst x t).map₂ l) := by
  induction l <;> simp [ConstrUnifier, map₂]
  case cons hd tl ih =>
  rw [← Unifier.eq_apply_varSubst, ih]
  . exact Eq.to_iff rfl
  . grind

@[grind =>]
lemma not_isSome_unifyStep_of_isUnifyFail : isUnifyFail t u → ¬ (unifyStep ⟨τ, (t, u)::l⟩).isSome := by
  induction t <;> induction u <;> simp [isUnifyFail, unifyStep]

theorem unifyStep_complete (σ : Subst) (st : UnifyState) (h : unifyStep st |>.isSome) :
  StateUnifier σ st → StateUnifier σ (unifyStep st |>.get h) := by
  let ⟨τ, l⟩ := st
  revert h τ
  apply unify_induction (P := fun l => _) l
  case _ => intros _ t u; grind
  case _ => simp only [unifyStep, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff,
    implies_true]
  case _ =>
    intros l x t _ τ _; simp only [StateUnifier, ConstrUnifier, unifyStep, Option.pure_def,
      Option.bind_eq_bind, Option.get_bind, varUnify_get_eq_varSubst, Option.get_some, and_imp]
    intros; rw [← ConstrUnifier.eq_apply_varSubst, ← SubstUnifier.eq_scomp_varSubst] <;> simp [Unifier, apply] at * <;> grind
  case _ =>
    intros l x t _ τ _; simp only [unifyStep, Option.pure_def, Option.isSome_some, StateUnifier,
      ConstrUnifier, Option.get_some, and_imp, forall_const]; grind
  case _ =>
    intros _ f g _ τ _
    simp only [StateUnifier, ConstrUnifier, unifyStep, Option.pure_def, Option.failure_eq_none,
      Option.get_ite, and_imp]
    grind
  case _ =>
    intros _ t₁ t₂ u₁ u₂ discard; clear discard
    intros τ _
    simp only [StateUnifier, ConstrUnifier, Unifier, apply, app.injEq, unifyStep, Option.pure_def,
      Option.get_some, and_imp]
    grind

def ConstrDisjVar (st : UnifyState) := Disjoint st.subst.dom (constrVars st.constraints)

lemma SubstUnifier.of_scomp_of_disjoint (σ₁ σ₂ σ₃ : Subst)
  (h₁ : Disjoint σ₁.dom σ₂.dom)
  (h₂ : SubstUnifier σ₃ (σ₁.scomp σ₂))
  : SubstUnifier σ₃ σ₂ := by
  simp [SubstUnifier] at *; intros x
  by_cases h:(x ∈ σ₂.dom)
  . have h':(x ∉ σ₁.dom) := by grind only [= Set.disjoint_left]
    have h'' := h₂ x
    simp only [scomp] at h''; simp only [dom] at h'
    grind only [usr Set.mem_setOf_eq, apply]
  . simp only [dom, ne_eq, Set.mem_setOf_eq, Decidable.not_not] at h; grind only [apply]

-- disjointness doesn't appear in the paper proof, annoyingly
theorem unifyStep_sound (σ : Subst) (st : UnifyState) (h : unifyStep st |>.isSome)
  (disj : ConstrDisjVar st)
  : StateUnifier σ (unifyStep st |>.get h) → StateUnifier σ st := by
  let ⟨τ, l⟩ := st
  revert h τ
  apply unify_induction (P := fun l => _) l
  case _ => intros _ t u; grind only [=> not_isSome_unifyStep_of_isUnifyFail]
  case _ => simp only [unifyStep, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff,
    implies_true]
  case _ =>
    intros l x t _ τ _; simp only [ConstrDisjVar, StateUnifier, unifyStep, Option.pure_def,
      Option.bind_eq_bind, Option.get_bind, varUnify_get_eq_varSubst, Option.get_some,
      ConstrUnifier, and_imp]
    intros h₁ h₂
    -- Some tedium here
    have h₃ : Unifier σ (var x) t := by
      simp only [constrVars, Finset.union_assoc, Finset.coe_union, Set.disjoint_union_right] at h₁
      have h₄ : Disjoint τ.dom (varSubst x t).dom := by
        apply Disjoint.mono_right (c:={x})
        . apply varSubst_dom_subset
        . simp only [vars] at h₁; simp; grind
      have h₅ := SubstUnifier.of_scomp_of_disjoint _ _ _ h₄ h₂
      simp only [Unifier, apply]
      have h₆ := h₅ x
      simp only [varSubst_self] at h₆; trivial
    rw [← ConstrUnifier.eq_apply_varSubst]; rw [← SubstUnifier.eq_scomp_varSubst] at h₂
    . grind only
    . apply h₃
    . apply h₃
  case _ =>
    intros l x t _ _ τ _; simp only [ConstrDisjVar, StateUnifier, unifyStep, Option.pure_def,
      Option.get_some, ConstrUnifier, and_imp]
    grind only [→ Unifier.symm]
  case _ =>
    intros _ f g _ τ h
    simp only [StateUnifier, unifyStep, Option.pure_def, Option.failure_eq_none, Option.get_ite,
      ConstrUnifier, Unifier, apply, func.injEq, and_imp]
    simp only [unifyStep, Option.pure_def, Option.failure_eq_none, Option.isSome_ite] at h; grind only
  case _ =>
    intros _ t₁ t₂ u₁ u₂ discard; clear discard
    intros τ _
    simp only [StateUnifier, unifyStep, Option.pure_def, Option.get_some, ConstrUnifier, Unifier,
      apply, app.injEq, and_imp]
    grind only

lemma Option.isSome_bind_of_isSome {α β} (x : Option α) (f : α → Option β) (h : x.isSome) (h' : ∀ y, f y |>.isSome)
  : (x.bind f).isSome := by
  cases x <;>
  grind

theorem unifyStep_progress (σ : Subst) (st : UnifyState)
  (h₁ : ¬ st.constraints.isEmpty)
  (h₂ : StateUnifier σ st) : (unifyStep st |>.isSome) := by
  revert h₁ h₂
  have ⟨τ, l⟩ := st
  apply unify_induction (P := fun l => _) l <;> intros l <;> simp [StateUnifier, ConstrUnifier] <;> intros
  . grind only [=> not_unifier_of_isUnifyFail]
  . simp only [List.isEmpty_nil, not_true_eq_false] at l
  case _ x t _ _ _ _ =>
    simp only [unifyStep, Option.pure_def, Option.bind_eq_bind]
    have h' := varUnify_isSome_of_unifier x t σ (by trivial)
    apply Option.isSome_bind_of_isSome; trivial
    grind only [= Option.isSome_some]
  case _ x t _ _ _ h _ =>
    simp only [unifyStep, Option.pure_def, Option.isSome_some]
  . simp only [Unifier, apply, func.injEq] at *; simp only [unifyStep, Option.pure_def,
    Option.failure_eq_none, Option.isSome_ite]; trivial
  . simp only [Unifier, apply, app.injEq] at *; simp only [unifyStep, Option.pure_def,
    Option.isSome_some]

lemma vars_apply_varSubst_subset x (t u : Term) : (u.apply (varSubst x t)).vars ⊆ t.vars ∪ (u.vars \ {x}) := by
    apply apply_vars_subset; intros y h
    by_cases h':(y = x) <;> simp [h', vars]
    grind only

lemma constrVars_apply_varSubst_subset x t l : constrVars ((varSubst x t).map₂ l) ⊆ t.vars ∪ constrVars l := by
  induction l <;> simp [constrVars, Subst.map₂]
  case cons hd tl ih =>
    let ⟨u₁, u₂⟩ := hd
    simp
    have h₁ := vars_apply_varSubst_subset x t u₁
    have h₂ := vars_apply_varSubst_subset x t u₂
    apply Finset.union_subset
    . grind
    . apply Finset.union_subset
      . grind only [= Finset.subset_iff, = Finset.mem_union, = Finset.mem_sdiff]
      . have h' : -- hmpf
         constrVars (List.map (fun x_1 => (x_1.1.apply (varSubst x t), x_1.2.apply (varSubst x t))) tl) =
         constrVars ((varSubst x t).map₂ tl) := by eq_refl
        rw [h']
        grind only [= Finset.subset_iff, = Finset.mem_union]


lemma Disjoint.apply_varSubst (t u : Term) (h : Disjoint S t.vars) (h' : Disjoint S u.vars)
 : Disjoint S (u.apply (varSubst x t)).vars := by
  have h₂ : (u.apply (varSubst x t)).vars ⊆ u.vars ∪ t.vars := by
    apply apply_vars_subset; intros y h
    by_cases h':(y = x) <;> simp [h', vars]
    grind only
  apply Disjoint.mono_right (c := u.vars ∪ t.vars); trivial
  apply Disjoint.sup_right <;> trivial

@[grind →]
lemma unifyStepVarCases (t : Term) (h : unifyStep ⟨τ, (var x, t)::l⟩ |>.isSome) :
  t = var x ∨ x ∉ t.vars := by
  have h' := varUnify_some_iff x t
  simp only [unifyStep, Option.pure_def, Option.bind_eq_bind] at h
  cases h'':(varUnify x t) <;> simp [h''] at h
  simp only [h'', Option.isSome_some, true_iff] at h'
  grind

lemma Disjoint.singleton_varSubst (x : Var) (t u : Term) (h : x ∉ t.vars)
 : Disjoint {x} (u.apply (varSubst x t)).vars := by
  induction u <;> simp [apply, vars]
  case _ y =>
    by_cases h':(y = x) <;> simp [h', vars] <;> grind
  case _ => simp at *; grind

lemma Disjoint.singleton_constrVars_varSubst {x : Var} {t : Term} (h : x ∉ t.vars)
 : Disjoint {x} (constrVars <| (varSubst x t).map₂ l) := by
  induction l <;> simp [Subst.map₂, constrVars]
  case _ _ ih =>
  have h' := Disjoint.singleton_varSubst (x := x) t
  simp only [Finset.disjoint_singleton_left] at *
  constructor; grind
  constructor; grind
  apply ih


theorem unifyDisj (st : UnifyState) (h : unifyStep st |>.isSome)
  : ConstrDisjVar st → ConstrDisjVar (unifyStep st |>.get h) := by
  revert h
  let ⟨τ, l⟩ := st
  apply unify_induction (P := fun l => _) l
  . grind only [=> not_isSome_unifyStep_of_isUnifyFail]
  . intros h; simp only [unifyStep, Option.isSome_none, Bool.false_eq_true] at h
  . intros l x t dummy h; clear dummy
    simp only [ConstrDisjVar, constrVars, vars, Finset.singleton_union, Finset.insert_union,
      Finset.coe_insert, Finset.coe_union, Set.disjoint_insert_right, Set.disjoint_union_right,
      unifyStep, Option.pure_def, Option.bind_eq_bind, Option.get_bind, varUnify_get_eq_varSubst,
      Option.get_some, and_imp]
    intros
    cases (unifyStepVarCases _ h)
    case _ isVar =>
      simp only [isVar, varSubst_self_eq_idSubst, scomp_idSubst, map₂_id]
      trivial
    case _ =>
      apply Disjoint.mono_left (b:= (τ.dom ∪ {x}))
      . have h := Subst.scomp_dom_subset τ (varSubst x t)
        have h' := varSubst_dom_subset x t
        simp only [Set.union_singleton, Set.le_eq_subset]; grind only [= Set.subset_def, = Set.mem_insert_iff, = Set.mem_union,
          = Set.mem_singleton_iff] -- This one is a bit awkard to grind
      . simp; constructor
        . have h' := Disjoint.singleton_constrVars_varSubst (x:=x) (t:=t) (l:=l)
          simp only [Finset.disjoint_singleton_left] at h'; grind only
        . apply Disjoint.mono_right (c:= ↑(t.vars ∪ constrVars l))
          . apply constrVars_apply_varSubst_subset -- miracle
          . simp only [Finset.coe_union, Set.disjoint_union_right]; grind only
  . intros l x t nvar dummy h; clear dummy
    simp only [ConstrDisjVar, constrVars, vars, Finset.union_singleton, Finset.insert_union,
      Finset.coe_insert, Finset.coe_union, Set.disjoint_insert_right, Set.disjoint_union_right,
      unifyStep, Option.pure_def, Option.get_some, Finset.singleton_union, imp_self]
  . intros _ _ _ _ _; simp only [ConstrDisjVar, constrVars, vars, Finset.union_idempotent,
    Finset.empty_union, unifyStep, Option.pure_def, Option.failure_eq_none, Option.get_ite,
    imp_self]
  . intros _ _ _ _ _; simp only [unifyStep, Option.pure_def, Option.bind_eq_bind,
    Option.failure_eq_none, ConstrDisjVar, Option.isSome_some, constrVars, vars, Finset.union_assoc,
    Finset.coe_union, Set.disjoint_union_right, Option.get_some, and_imp, forall_const]
    grind only

-- For some reason, an essential trick is the idempotence of the constructed thing:
def Subst.Idem (σ : Subst) := σ.scomp σ = σ

@[simp]
lemma Subst.IdemApp (σ : Subst) (h : σ.Idem) (t : Term) :
  (t.apply σ).apply σ = t.apply σ := by
  simp only [Idem] at h
  have h' : (t.apply σ).apply σ = t.apply (σ.scomp σ) := by simp only [scomp_apply]
  grind

@[simp]
lemma Subst.IdemVar (σ : Subst) (h : σ.Idem) (x : Var) :
  (σ x).apply σ = σ x := by
  have h' := Subst.IdemApp σ h (var x)
  simp only [apply] at h'
  trivial

abbrev IdemState (st : UnifyState) := st.subst.Idem ∧ ConstrDisjVar st

-- A sufficient (and necessary, but whatever) condition for being idempotent:
def Subst.IdemAux (σ : Subst) := ∀ x, Disjoint σ.dom (σ x).vars

lemma Subst.idem_of_idemAux (σ : Subst) : σ.IdemAux → σ.Idem := by
  simp only [IdemAux, Idem]; intros; funext y
  apply Term.apply_eq_of_disjoint_dom; grind

lemma substVarIdem x t (h : x ∉ t.vars) : (varSubst x t).Idem := by
  apply Subst.idem_of_idemAux; intros y
  have h' := varSubst_dom_subset x t
  by_cases h'' : (y = x) <;> simp [h'', vars] <;> grind only [= Set.subset_def, = Set.disjoint_left,
    = disjoint_comm, = Finset.mem_coe, = Set.mem_singleton_iff]


lemma apply_eq_iff_vars_fixed (σ : Subst) (t : Term) (h : t.apply σ = t)
  : ∀ x ∈ t.vars, σ x = var x := by
  induction t <;> simp only [vars, apply] at * <;> grind

@[simp]
lemma Subst.idem_apply_var (σ : Subst) (h : σ.Idem) x
  : (σ x).apply σ = σ x := by rw [← scomp, h]

lemma Subst.idemAux_of_idem (σ : Subst) : σ.Idem → σ.IdemAux := by
  simp [IdemAux]; intros h x
  have h : ∀ y ∈ ↑(σ x).vars, y ∉ σ.dom := by
    intros y h'
    have h'' := apply_eq_iff_vars_fixed σ (σ x) (by simp [h]) _ h'
    simp only [dom, ne_eq, Set.mem_setOf_eq, Decidable.not_not]; trivial
  grind only [= Set.disjoint_left, = Finset.mem_coe]

lemma Subst.idem_iff_idemAux (σ : Subst) : σ.Idem ↔ σ.IdemAux := by
  grind only [idemAux_of_idem, idem_of_idemAux]

lemma Subst.idem_scomp (σ : Subst) (x : Var) (t : Term)
  (h₁ : σ.Idem)
  (h₂ : x ∉ t.vars)
  (h₃ : Disjoint σ.dom t.vars)
  : σ.scomp (varSubst x t) |>.Idem := by
  rw [Subst.idem_iff_idemAux] at *
  simp only [IdemAux, scomp]; intros y
  apply Disjoint.mono_left (b := σ.dom ∪ {x})
  . have h := Subst.scomp_dom_subset σ (varSubst x t)
    have h' := varSubst_dom_subset x t
    simp only [Set.union_singleton, Set.le_eq_subset]; grind only [= Set.subset_def,
      = Set.mem_insert_iff, = Set.mem_union, = Set.mem_singleton_iff]
  . apply Disjoint.mono_right (c := ↑(t.vars ∪ ((σ y).vars \ {x})))
    . apply vars_apply_varSubst_subset x t (σ y)
    . simp only [Set.union_singleton, Finset.coe_union, Finset.coe_sdiff, Finset.coe_singleton,
      Set.disjoint_union_right, Set.disjoint_insert_left, SetLike.mem_coe, Set.mem_diff,
      Set.mem_singleton_iff, not_true_eq_false, and_false, not_false_eq_true, true_and]
      simp only [IdemAux] at h₁
      grind only [= Set.disjoint_left, = disjoint_comm, = Set.mem_diff]

theorem unifyStepIdem (st : UnifyState) (h : unifyStep st |>.isSome)
  : IdemState st → IdemState (unifyStep st |>.get h) := by
  intros idemSt
  have disjConstr : ConstrDisjVar ((unifyStep st).get h) := by
    apply unifyDisj; apply idemSt.2
  simp only [IdemState]; refine (And.intro ?X (by trivial))
  revert idemSt h
  let ⟨τ, l⟩ := st
  apply unify_induction (P := fun l => _) l
  . grind only [=> not_isSome_unifyStep_of_isUnifyFail]
  . simp only [unifyStep, Option.isSome_none, Bool.false_eq_true, and_imp, IsEmpty.forall_iff]
  . intros l x t discard isSome idemSt; clear discard
    simp only [unifyStep, Option.pure_def, Option.bind_eq_bind, Option.get_bind,
      varUnify_get_eq_varSubst, Option.get_some]; intros disj
    by_cases h: (t = var x); simp [h]; apply idemSt.1
    apply Subst.idem_scomp
    . apply idemSt.1
    . grind only [→ unifyStepVarCases]
    . have h := idemSt.2
      simp only [ConstrDisjVar, constrVars, Finset.union_assoc, Finset.coe_union,
        Set.disjoint_union_right] at h
      grind only
  . intros l x t _ discard isSome idemSt; clear discard
    simp only [unifyStep, Option.pure_def, Option.get_some]; intros; grind
  . simp only [unifyStep, Option.pure_def, Option.bind_eq_bind, Option.failure_eq_none, and_imp,
    Option.isSome_ite, Option.get_ite, forall_apply_eq_imp_iff]; intros; trivial
  . simp only [unifyStep, Option.pure_def, Option.bind_eq_bind, Option.failure_eq_none, and_imp,
    Option.isSome_some, Option.get_some, forall_const]; intros; trivial

lemma unify_auxUnifyStepIsSome (st : UnifyState)
  (nNil : ¬ st.constraints.isEmpty)
  (nNone : unify_aux st |>.isSome)
  : unifyStep st |>.isSome := by
  let ⟨τ, constr⟩ := st
  cases constr
  . simp only [List.isEmpty_nil, not_true_eq_false] at nNil
  case _ head tail =>
    unfold unify_aux at nNone
    simp only at nNone
    cases h:(unifyStep ⟨τ, head::tail⟩)
    . simp only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceDIte] at nNone
    . trivial

lemma unify_aux_induction (P : UnifyState → Prop)
  (st : UnifyState)
  (start : P st)
  (step : ∀ st (h : unifyStep st |>.isSome), P st → P (unifyStep st |>.get h))
  (h : unify_aux st |>.isSome)
   : P (unify_aux st |>.get h) := by
  unfold unify_aux
  let ⟨τ, constr⟩ := st
  cases constr <;> simp only [Option.pure_def, Option.get_some]; trivial
  case _ head tail =>
    have stepSome := unify_auxUnifyStepIsSome ⟨τ, head::tail⟩ (by simp) h
    simp only [stepSome, ↓reduceDIte]
    apply unify_aux_induction
    . apply step
      trivial
    . grind only
  termination_by ltState st
  decreasing_by
    have h := ltState_decreasing (st:=⟨τ, constr⟩) (h:= by grind)
    grind only

lemma unify_aux_inductionBack (P : UnifyState → Prop)
  (st : UnifyState)
  (h : unify_aux st |>.isSome)
  (ending : P (unify_aux st |>.get h))
  (step : ∀ st (h : unifyStep st |>.isSome), P (unifyStep st |>.get h) → P st)
   : P st := by
  let ⟨τ, constr⟩ := st
  unfold unify_aux at ending
  cases constr <;> simp only at ending; trivial
  case _ head tail =>
    have stepSome := unify_auxUnifyStepIsSome ⟨τ, head::tail⟩ (by simp) h
    simp only [stepSome] at ending
    apply step
    . apply unify_aux_inductionBack
      . apply ending -- what's happening here?
      . trivial
  termination_by ltState st
  decreasing_by
    have h := ltState_decreasing (st:=⟨τ, constr⟩) (h:= by grind)
    grind only

-- God I hate this lemma. Basically we're traveling both forward and backwards to our
-- destination. Forward for the Q's and backword for the P's.
lemma unify_aux_inductionBi
  (P : UnifyState → Prop)
  (Q : UnifyState → Prop)
  (st : UnifyState)
  (h : unify_aux st |>.isSome)
  (beginning : Q st)
  (stepForth : ∀ st (h : unifyStep st |>.isSome), Q st → Q (unifyStep st |>.get h))
  (ending : P (unify_aux st |>.get h))
  (stepBack : ∀ st (h : unifyStep st |>.isSome), Q st → P (unifyStep st |>.get h) → P st)
   : P st := by
  let ⟨τ, constr⟩ := st
  unfold unify_aux at ending
  cases constr <;> simp only at ending; trivial
  case _ head tail =>
    have stepSome := unify_auxUnifyStepIsSome ⟨τ, head::tail⟩ (by simp) h
    simp only [stepSome] at ending
    have h : Q ⟨τ, head::tail⟩ := by trivial
    apply stepBack ⟨τ, head::tail⟩ (by grind) h _
    . apply unify_aux_inductionBi (Q := Q) (st := (unifyStep { subst := τ, constraints := head :: tail }).get (by trivial))
      . apply stepForth; trivial
      . trivial
      . apply ending
      . trivial
  termination_by ltState st
  decreasing_by
    have h := ltState_decreasing (st:=⟨τ, constr⟩) (h:= by grind)
    grind only


-- Ok now we're ready to prove actual soundness and completeness of the unification process.
lemma unify_auxComplete
  (unif : StateUnifier σ st)
  (h : unify_aux st |>.isSome)
   : StateUnifier σ (unify_aux st |>.get h) := by
  apply unify_aux_induction <;> grind only [unifyStep_complete]

lemma unify_auxIdem
  (unif : IdemState st)
  (h : unify_aux st |>.isSome)
   : IdemState (unify_aux st |>.get h) := by
  apply unify_aux_induction <;> grind only [unifyStepIdem]

@[simp]
lemma unify_auxEmptyConstr
  (h : unify_aux st |>.isSome)
  : (unify_aux st |>.get h).constraints = [] := by
  let ⟨τ, l⟩ := st
  cases l
  . simp [unify_aux]
  case _ head tail =>
    unfold unify_aux
    simp only
    have stepSome := unify_auxUnifyStepIsSome ⟨τ, head::tail⟩ (by simp) h
    simp only [stepSome]
    apply unify_auxEmptyConstr
  termination_by ltState st
  decreasing_by
    have h := ltState_decreasing (st:=⟨τ, l⟩) (h:= by grind)
    grind only

lemma unify_auxEnding
  (unif : IdemState st)
  (h : unify_aux st |>.isSome)
  : StateUnifier (unify_aux st |>.get h).subst (unify_aux st |>.get h) := by
  simp only [StateUnifier, SubstUnifier, unify_auxEmptyConstr, ConstrUnifier, and_true]
  intros x
  have h' := unify_auxIdem (st:=st) unif h |>.1
  have h'' := Subst.IdemVar (σ := (unify_aux st).get h |>.subst) h' x
  grind only

lemma unify_auxSound
  (unif : IdemState st)
  (h : unify_aux st |>.isSome)
  : StateUnifier (unify_aux st |>.get h).subst st := by
  apply unify_aux_inductionBi (Q := IdemState) (P := fun st' =>
    StateUnifier (unify_aux st |>.get h).subst st')
  . trivial
  . grind only [!unifyStepIdem]
  . grind only [!unify_auxEnding]
  . intros st' h' idemSt unifierUnify
    apply unifyStep_sound
    . apply idemSt.2
    . trivial
  . trivial

lemma idemStateId : IdemState ⟨idSubst, l⟩ := by
  simp [IdemState]; constructor <;> simp [Idem, ConstrDisjVar]

theorem unifySound (h : unify t u |>.isSome) : Unifier (unify t u |>.get h) t u := by
  simp only [unify, Option.get_map]
  simp only [unify, Option.isSome_map] at h
  have h' : IdemState ⟨idSubst, [(t, u)]⟩ := by apply idemStateId
  have h'' := unify_auxSound (by trivial) (by trivial)
  simp only [StateUnifier, ConstrUnifier, and_true] at h''
  grind only

-- the crucial lemma 4.6.2 from TRAAT
-- lemma unify_auxUnifier

lemma StateUnifierIsUnifier (σ : Subst) (t u : Term) (unifies: Unifier σ t u)
  : StateUnifier σ ⟨idSubst, [(t, u)]⟩ := by
  simp only [StateUnifier, SubstUnifier, apply, implies_true, ConstrUnifier, and_true, true_and]
  grind

lemma unify_complete_aux
  (unif : StateUnifier σ st)
  (h : unify_aux st |>.isSome)
  : ∃ τ, σ = (unify_aux st |>.get h).subst.scomp τ := by
  exists σ
  funext x
  have h' := unify_auxComplete unif h
  simp only [StateUnifier, SubstUnifier, unify_auxEmptyConstr] at h'
  grind only [scomp]

theorem unify_auxProgress
  (unif : StateUnifier σ st)
 : unify_aux st |>.isSome := by
 -- apply unify_aux_induction -- well crap
 have h' := unifyStep_progress σ st
 let ⟨τ, cstrs⟩ := st
 cases cstrs
 case nil => simp only [unify_aux, Option.pure_def, Option.isSome_some]
 case cons head tail =>
  unfold unify_aux
  simp only [List.isEmpty_cons, Bool.false_eq_true, not_false_eq_true, forall_const] at h'
  have h' := h' unif
  simp only [h']
  apply unify_auxProgress (σ := σ)
  apply unifyStep_complete; grind only
termination_by ltState st
decreasing_by
  grind only [!ltState_decreasing]

theorem unify_progress
  (unif : Unifier σ t u)
 : unify t u |>.isSome := by
 simp only [unify, Option.isSome_map]
 apply unify_auxProgress (σ := σ)
 apply StateUnifierIsUnifier; grind

lemma unify_progress'
  (unif : Unify t u)
  : unify t u |>.isSome :=
  by
    have ⟨σ, _⟩ := unif
    apply unify_progress; trivial

lemma unify_complete'
  (unif : Unifier σ t u)
  (h : unify t u |>.isSome)
  : ∃ τ, σ = (unify t u |>.get h).scomp τ := by
  simp only [unify, Option.get_map]
  apply unify_complete_aux
  apply StateUnifierIsUnifier; grind only

theorem unify_complete
  (unif : Unifier σ t u)
  : ∃ τ, σ = (unify t u |>.get (unify_progress unif)).scomp τ := by
  grind only [unify_complete']

end Unification

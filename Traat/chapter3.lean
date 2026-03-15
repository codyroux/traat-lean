import Traat.chapter2

section Unification

open Term Subst

def Unifier (σ : Subst) (t u : Term) : Prop := t.apply σ = u.apply σ

def Unifies (t u : Term) : Prop := ∃ σ, Unifier σ t u

def varSubst (x : Var) (t : Term) : Subst := fun y => if y = x then t else var y

@[simp]
lemma varSubstNEq (h : y ≠ x) : varSubst x t y = var y := by grind [varSubst]

@[simp]
lemma varSubstEq : varSubst x t x = t := by grind [varSubst]

@[grind →]
lemma unifierSymm (σ : Subst) (t u : Term) (_ : Unifier σ t u) : Unifier σ u t := by
  simp [Unifier] at *; grind

def varUnify (x : Var) (t : Term) : Option Subst :=
  if (x ∈ t.vars ∧ t ≠ var x) then none
  else varSubst x t

@[grind =]
lemma varUnify_some_iff (x : Var) (t : Term) :
  (varUnify x t).isSome ↔ (x ∉ t.vars ∨ t = var x) := by grind [varUnify]

@[grind .]
lemma varsSubApply₁ (t₁ t₂ : Term) : t₁.vars ⊆ (t₁ @@ t₂).vars := by
  simp [Term.vars]

@[grind .]
lemma varsSubApply₂ (t₁ t₂ : Term) : t₂.vars ⊆ (t₁ @@ t₂).vars := by
  simp [Term.vars]

lemma substDom (t : Term) (σ τ : Subst) (h : ∀ x ∈ t.vars, σ x = τ x) : t.apply σ = t.apply τ := by
  induction t <;> simp [Term.apply, Term.vars] at * <;> grind only

@[simp, grind =]
lemma idSubst_apply (t : Term) : t.apply idSubst = t := by grind

@[simp, grind =]
lemma scompIdsubst (σ : Subst) : σ.scomp idSubst = σ := by
  funext; simp [scomp]

lemma varDom (t : Term) (σ : Subst) (h : Disjoint σ.dom t.vars) : t.apply σ = t := by
  have h' : t = t.apply idSubst := by grind
  have h'' : ∀ x ∈ t.vars, σ x = idSubst x := by
    intros x; simp [idSubst]
    rw [Set.disjoint_right] at h
    simp [dom] at h
    apply h
  grind [substDom]

lemma varSubstDom (x : Var) (t : Term) :
  (varSubst x t).dom ⊆ {x} := by
  simp [dom, varSubst]

lemma varSubstDom' (x : Var) (t : Term) (_ : t ≠ var x) :
  (varSubst x t).dom = {x} := by simp [dom, varSubst]; grind

lemma varSubstDomCases (x : Var) (t : Term) :
  (varSubst x t).dom = {x} ∨ (varSubst x t).dom = {} := by
  have h := varSubstDom x t
  grind

lemma varUnifyDom (x : Var) (t : Term) (h : varUnify x t |>.isSome) :
  (varUnify x t |>.get h).dom ⊆ {x} := by
  simp [dom, varUnify, varSubst]

@[simp]
lemma varUnifyId (x : Var) (h : varUnify x (var x) |>.isSome) :
  (varUnify x (var x)).get h = idSubst := by
  funext y
  by_cases h : y = x
  . simp [varUnify, idSubst, h]
  . simp [varUnify, h]

@[simp]
lemma varUnifyNId (x : Var) (t : Term) (h₁ : varUnify x t |>.isSome) :
  (varUnify x t).get h₁ = varSubst x t := by
  funext; simp [varUnify]

lemma varUnifyUnif (x : Var) (t : Term) (h : varUnify x t |>.isSome) :
  (varUnify x t).get h x = t.apply ((varUnify x t).get h) := by
  have h₁ : x ∉ t.vars ∨ t = var x := by
    simp [varUnify] at h; grind
  cases h₁
  case _ =>
    have h₂ : Disjoint ((varUnify x t).get h).dom t.vars := by
      grind [varUnifyDom]
    rw [varDom]; simp [varUnify]; trivial
  case _ h =>
    simp [h, Term.apply, varUnify]

lemma varUnifyMGU_aux (x : Var) (t : Term) (σ : Subst)
  (hasUnifier : σ x = t.apply σ)
  : ∃ τ : Subst, (varSubst x t).scomp τ = σ := by
  exists (fun y => if y = x then t.apply σ else σ y)
  funext y
  by_cases h:(y = x); simp [h, scomp]
  . rw [substDom t _ σ] <;> grind
  . simp [scomp, h, Term.apply]

lemma varUnifyMGU (x : Var) (t : Term) (σ : Subst)
  (unifies : varUnify x t |>.isSome)
  (hasUnifier : σ x = t.apply σ)
  : let mgu := varUnify x t |>.get unifies
  ∃ τ : Subst, mgu.scomp τ = σ := by
  simp [varUnify]
  apply varUnifyMGU_aux; trivial

lemma memSize (x : Var) (t : Term) (σ : Subst) (mem : x ∈ t.vars) (ne : t ≠ var x) :
  sizeOf (σ x) < sizeOf (t.apply σ) := by
  induction t
  case _ => grind [vars]
  case _ => grind [vars]
  case _ t₁ t₂ ih₁ ih₂ =>
    simp [apply]; simp [vars] at mem
    cases mem
    . by_cases eq:(t₁ = var x)
      . simp [eq, apply]; grind
      . grind
    . by_cases eq:(t₂ = var x)
      . simp [eq, apply]; grind
      . grind

lemma varUnifyNotSome (x : Var) (t : Term) (σ : Subst)
  (hasUnifier : σ x = t.apply σ) :
  varUnify x t |>.isSome := by
  by_contra
  have h : (varUnify x t) |>.isNone := by revert this; simp
  have h' : x ∈ t.vars := by grind [varUnify]
  have h'' : t ≠ var x := by grind [varUnify]
  have h₃ := memSize x t σ (by trivial) (by trivial)
  grind

#print Decidable
#print DecidableEq

#synth DecidableEq Term

instance domDec {σ : Subst} {x : Var} : Decidable (x ∈ σ.dom) :=
  if h : σ x = var x then .isFalse (by simp [dom]; exact h) else .isTrue h

@[simp]
def Subst.join (σ₁ σ₂ : Subst) : Subst :=
  fun x => if x ∈ σ₁.dom then σ₁ x else σ₂ x

lemma joinDisjCommut (σ₁ σ₂ : Subst) (disj : Disjoint σ₁.dom σ₂.dom) : σ₁.join σ₂ = σ₂.join σ₁ := by
  funext x; simp
  by_cases h : (x ∈ σ₁.dom)
  . simp [Set.disjoint_left] at *
    grind
  . simp [h]
    simp [dom] at *; grind

@[simp]
lemma joinDom (σ₁ σ₂ : Subst) : (σ₁.join σ₂).dom = σ₁.dom ∪ σ₂.dom := by
  simp [join, dom, setOf, Union.union, Set.union, Membership.mem, Set.Mem]
  funext x; grind

@[simp]
lemma scompDom (σ₁ σ₂ : Subst) : (σ₁.scomp σ₂).dom ⊆ σ₁.dom ∪ σ₂.dom := by
  simp [dom]; intro x; simp [scomp]
  rw [← Classical.not_and_iff_not_or_not]
  intros; grind [apply]

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
  simp [idSubst, dom]

@[simp]
lemma Subst.map₂_id (l : List (Term × Term)) : idSubst.map₂ l = l := by
  induction l <;> grind [Subst.map₂]

lemma substCodom (t : Term) (σ : Subst) (codom_inc : ∀ x ∈ t.vars, (σ x).vars ⊆ S) :
  (t.apply σ).vars ⊆ S := by
  induction t <;> simp [Term.apply, Term.vars] <;> simp [Term.vars] at codom_inc <;> grind

lemma excludeCodom (t : Term) (σ : Subst) (x : Var) (h : ∀ y, x ∉ (σ y).vars) : x ∉ (t.apply σ).vars := by
  induction t <;> simp [apply, vars] <;> grind

lemma substMapDom (l : List (Term × Term)) (σ : Subst)
  (codom_inc : ∀ x ∈ constrVars l, (σ x).vars ⊆ S) :
  constrVars (σ.map₂ l) ⊆ S := by
  revert codom_inc; induction l <;> simp [constrVars, Subst.map₂]
  case _ head tail ih =>
    intros codom_inc
    rw [Finset.union_subset_iff]; rw [Finset.union_subset_iff]
    apply And.intro
    . grind [substCodom]
    . apply And.intro; grind [substCodom]
      apply ih; grind

lemma excludeConstrCodom (l : List (Term × Term)) (σ : Subst) (x : Var)
  (h : ∀ y, x ∉ (σ y).vars)
  : x ∉ constrVars (σ.map₂ l) := by
  induction l <;> simp [Subst.map₂, constrVars]
  case _ t₁ t₂ ih =>
    have h' := fun t => excludeCodom t σ x h
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

#synth SizeOf (List ℕ)

#print List._sizeOf_1

#print Term._sizeOf_1

noncomputable def constrSize : List (Term × Term) → ℕ
| [] => 0
| (t₁, t₂) :: cstrs => 1 + sizeOf t₁ + sizeOf t₂ + (constrSize cstrs)

def isVar : Term → Bool
| var _ => true
| _ => false

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

#print Prod.Lex

lemma cardExcludedMem α (s s' : Finset α) (x : α) :
  s ≤ s' → x ∈ s' → x ∉ s → s.card < s'.card := by
  simp; intros; apply Finset.card_lt_card; grind

@[grind →]
lemma unifyStep_isSome_var
  (h : (unifyStep { subst := subst, constraints := (var x, u) :: tail }).isSome) :
  (varUnify x u).isSome := by
  revert h; simp [unifyStep, Option.bind]
  split <;> grind

-- This is the clever bit: we get rid of a variable with that `varUnify`,
-- which decreases the second leg of the measure.
private lemma constrRemoveVar
  (h : (varUnify x u).isSome)
  (h' : u ≠ var x) :
  (constrVars ((varSubst x u).map₂ tail)).card <
  (insert x (u.vars ∪ constrVars tail)).card := by
  apply cardExcludedMem (x := x)
  . have vu_some : (varUnify x u).isSome := by grind
    have h' := substMapDom (S := u.vars ∪ constrVars tail) tail (varSubst x u)
    apply Finset.Subset.trans (s₂ := u.vars ∪ constrVars tail)
    . apply h'
      intros y h
      by_cases eq:(y = x)
      . rw [eq]; simp
      . simp [eq, Term.vars]
        grind
    . simp
  . grind
  . have vu_some : (varUnify x u).isSome := by grind
    apply excludeConstrCodom
    intros y; by_cases h':(y = x)
    . simp [h']; grind
    . simp [h', Term.vars]; grind

lemma varSubstId (t : Term) : t.apply (varSubst x (var x)) = t := by
  induction t <;> simp [apply, varSubst] <;> grind

@[simp]
lemma varSubstId' : (varSubst x (var x)) = idSubst := by
  funext; simp [idSubst, varSubst]; grind

@[simp]
lemma varSubstIdMap : (varSubst x (var x)).map₂ l = l := by
  induction l <;> simp [map₂]

#synth LT (ℕ × ℕ)
#print Prod.instPreorder

-- This is quite a bit more tedious than I'd like.
lemma decltState : Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
  (ltState ((unifyStep st).get h)) (ltState st) := by
  have ⟨_, l⟩ := st
  rcases l with _ | ⟨⟨t, u⟩, tail⟩ <;> simp [unifyStep]
  case nil => simp [unifyStep] at h
  case cons =>
  cases t
  case _ x =>
    by_cases (u = var x)
    case _ h' =>
      apply Prod.Lex.right' <;> simp [h']
      . simp [constrVars]
        apply Finset.card_mono
        simp [LE.le]
        grind
      . apply Prod.Lex.left
        simp [constrSize]
    case _ =>
      apply Prod.Lex.left; simp [constrVars, Term.vars]
      apply constrRemoveVar <;> grind
  case _ =>
    cases u
    case _ f x =>
      apply Prod.Lex.right; apply Prod.Lex.right; simp [rhsVarSize, isVar]
    case _ =>
      apply Prod.Lex.right' <;> simp [constrVars]
      . apply Finset.card_mono
        simp [LE.le]; grind
      . apply Prod.Lex.left
        simp [constrSize]
    case _ => simp [unifyStep] at h
  case _ t₁ t₂ =>
    cases u
    case _ x =>
      apply Prod.Lex.right'
      . simp [constrVars]; grind
      . apply Prod.Lex.right'
        . simp [constrSize]; grind
        . simp [rhsVarSize, isVar]
    case _ => simp [unifyStep] at h
    case _ =>
      apply Prod.Lex.right' <;> simp [constrVars]
      . apply Finset.card_mono
        simp [LE.le, Term.vars]; grind
      . simp [constrSize]; grind

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
    apply decltState

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
lemma isUnifyFailUnif : isUnifyFail t u → ¬ Unifier σ t u := by
  induction t <;> induction u <;> simp [isUnifyFail, Unifier, apply]

-- ugh this is ugly
private lemma unifyInduction (P : List (Term × Term) → Prop)
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
private lemma unifyInduction' (P : Term → Term → Prop)
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
    case _ => apply h₀; simp [isUnifyFail]
  case _ =>
    induction u
    case _ => grind
    case _ => apply h₀; simp [isUnifyFail]
    case _ => apply h₅ <;> grind


#print Subst.join

lemma substVarSubst (σ : Subst) (x : Var) (t : Term) (u : Term)
  (unify : t.apply σ = σ x)
  : (u.apply <| varSubst x t).apply σ = u.apply σ := by
  induction u <;> simp [apply]
  case var y =>
    by_cases h:(y = x) <;> simp [h, apply]
    . trivial
  case _ => grind

lemma unifierVarSubst (σ : Subst) (x : Var) (t : Term) (u₁ u₂ : Term)
  (unify₁ : t.apply σ = σ x)
  (unify₂ : Unifier σ u₁ u₂)
   : Unifier σ (u₁.apply (varSubst x t)) (u₂.apply (varSubst x t)) := by
  simp [Unifier] at unify₂
  simp [Unifier]; rw [substVarSubst] <;> try rw [substVarSubst] <;> grind
  grind

lemma constrUnifierVarSubst (σ : Subst) (x : Var) (t : Term) (l : List (Term × Term))
  (unify₁ : t.apply σ = σ x)
  (unify₂ : ConstrUnifier σ l)
   : ConstrUnifier σ ((varSubst x t).map₂ l) := by
  induction l <;> simp [Subst.map₂, ConstrUnifier]; simp [ConstrUnifier] at unify₂
  case _ head tl ih =>
  constructor
  . apply unifierVarSubst <;> grind
  . apply ih; grind

lemma unifierVarUnifSubst (σ : Subst) (x : Var) (t u₁ u₂ : Term)
  (h₁ : Unifier σ (var x) t)
  (h₂ : Unifier σ (u₁.apply (varSubst x t))
                  (u₂.apply (varSubst x t)))
  : Unifier σ u₁ u₂ := by
  revert h₂; simp [Unifier]
  rw [substVarSubst]; rw [substVarSubst]; grind
  . symm; apply h₁
  . symm; apply h₁

lemma unifierVarUnifConstrSubst (σ : Subst) (x : Var) (t : Term) l
  (h₁ : Unifier σ (var x) t)
  (h₂ : ConstrUnifier σ (varSubst x t |>.map₂ l))
  : ConstrUnifier σ l := by
  revert h₂; induction l <;> simp [ConstrUnifier, Subst.map₂]
  case _ hd tl ih =>
  cases hd
  case _ =>
    simp
    intros _ h; constructor
    . grind [unifierVarUnifSubst]
    . apply ih; apply h

@[simp]
lemma Subst.scompApply (σ τ : Subst) (t : Term)
  : t.apply (σ.scomp τ) = (t.apply σ).apply τ := by
  induction t <;> simp [apply, Subst.scomp]
  grind

lemma idempCompVarSubst (σ : Subst) x (t : Term)
  (h : σ x = t.apply σ)
  : (varSubst x t).scomp σ = σ := by
  funext y; simp [scomp]
  by_cases h':(y = x) <;> simp [h', apply]; grind

lemma unifyVarScompAux (σ τ : Subst)
  : Unifier (τ.scomp σ) u₁ u₂ =
    Unifier σ (u₁.apply τ) (u₂.apply τ) := by
  simp [Unifier]

lemma unifyVarTerm (σ : Subst) x (t : Term)
  (h₁ : σ x = t.apply σ)
  : Unifier σ u₁ u₂ =
    Unifier σ (u₁.apply (varSubst x t)) (u₂.apply (varSubst x t)) := by
  rw [← unifyVarScompAux, idempCompVarSubst]; trivial

lemma unifyVarSubst (σ τ : Subst) x (t : Term)
  (h₁ : σ x = t.apply σ)
  : SubstUnifier σ τ =
    SubstUnifier σ (τ.scomp (varSubst x t)) := by
  simp [SubstUnifier]
  constructor
  . intros h y
    simp [scomp]; rw [← scompApply, idempCompVarSubst]
    . apply h
    . trivial
  . intros h y
    have h := h y
    simp [scomp] at h
    rw [← scompApply, idempCompVarSubst] at h
    . apply h
    . trivial

lemma unifyVarConstr (σ : Subst) x (t : Term)
  (h₁ : σ x = t.apply σ)
  : ConstrUnifier σ l =
    ConstrUnifier σ ((varSubst x t).map₂ l) := by
  induction l <;> simp [ConstrUnifier, map₂]
  case cons hd tl ih =>
  rw [← unifyVarTerm, ih]
  . exact Eq.to_iff rfl
  . grind

@[grind =>]
lemma isUnifyFailUnifyStep : isUnifyFail t u → ¬ (unifyStep ⟨τ, (t, u)::l⟩).isSome := by
  induction t <;> induction u <;> simp [isUnifyFail, unifyStep]

theorem unifyStepComplete (σ : Subst) (st : UnifyState) (h : unifyStep st |>.isSome) :
  StateUnifier σ st → StateUnifier σ (unifyStep st |>.get h) := by
  let ⟨τ, l⟩ := st
  revert h τ
  apply unifyInduction (P := fun l => _) l
  case _ => intros _ t u; grind
  case _ => simp [unifyStep]
  case _ =>
    intros l x t _ τ _; simp [unifyStep, StateUnifier, ConstrUnifier]
    intros; rw [← unifyVarConstr, ← unifyVarSubst] <;> simp [Unifier, apply] at * <;> grind
  case _ =>
    intros l x t _ τ _; simp [unifyStep, StateUnifier, ConstrUnifier]; grind
  case _ =>
    intros _ f g _ τ _
    simp [unifyStep, StateUnifier, ConstrUnifier]
    grind
  case _ =>
    intros _ t₁ t₂ u₁ u₂ discard; clear discard
    intros τ _
    simp [StateUnifier, ConstrUnifier, unifyStep, Unifier, apply]
    grind

#check constrVars

#check varUnifyMGU_aux


def ConstrDisjVar (st : UnifyState) := Disjoint st.subst.dom (constrVars st.constraints)

lemma disjScompUnifier (σ₁ σ₂ σ₃ : Subst)
  (h₁ : Disjoint σ₁.dom σ₂.dom)
  (h₂ : SubstUnifier σ₃ (σ₁.scomp σ₂))
  : SubstUnifier σ₃ σ₂ := by
  simp [SubstUnifier] at *; intros x
  by_cases h:(x ∈ σ₂.dom)
  . have h':(x ∉ σ₁.dom) := by grind
    have h'' := h₂ x
    simp [scomp] at h''; simp [dom] at h'
    grind [apply]
  . simp [dom] at h; grind [apply]

-- disjointness doesn't appear in the paper proof, annoyingly
theorem unifyStepSound (σ : Subst) (st : UnifyState) (h : unifyStep st |>.isSome)
  (disj : ConstrDisjVar st)
  : StateUnifier σ (unifyStep st |>.get h) → StateUnifier σ st := by
  let ⟨τ, l⟩ := st
  revert h τ
  apply unifyInduction (P := fun l => _) l
  case _ => intros _ t u; grind
  case _ => simp [unifyStep]
  case _ =>
    intros l x t _ τ _; simp [unifyStep, StateUnifier, ConstrUnifier, ConstrDisjVar]
    intros h₁ h₂
    -- Some tedium here
    have h₃ : Unifier σ (var x) t := by
      simp [constrVars] at h₁
      have h₄ : Disjoint τ.dom (varSubst x t).dom := by
        apply Disjoint.mono_right (c:={x})
        . apply varSubstDom
        . simp [vars] at h₁; simp; grind
      have h₅ := disjScompUnifier _ _ _ h₄ h₂
      simp [Unifier, apply]
      have h₆ := h₅ x
      simp at h₆; trivial
    rw [← unifyVarConstr]; rw [← unifyVarSubst] at h₂
    . grind
    . apply h₃
    . apply h₃
  case _ =>
    intros l x t _ _ τ _; simp [unifyStep, StateUnifier, ConstrUnifier, ConstrDisjVar]
    grind
  case _ =>
    intros _ f g _ τ h
    simp [unifyStep, StateUnifier, ConstrUnifier, Unifier, apply]
    simp [unifyStep] at h; grind
  case _ =>
    intros _ t₁ t₂ u₁ u₂ discard; clear discard
    intros τ _
    simp [StateUnifier, ConstrUnifier, unifyStep, Unifier, apply]
    grind

lemma isSomeBindSome {α β} (x : Option α) (f : α → Option β) (h : x.isSome) (h' : ∀ y, f y |>.isSome)
  : (x.bind f).isSome := by
  cases x <;>
  grind

theorem unifyProgress (σ : Subst) (st : UnifyState)
  (h₁ : ¬ st.constraints.isEmpty)
  (h₂ : StateUnifier σ st) : (unifyStep st |>.isSome) := by
  revert h₁ h₂
  have ⟨τ, l⟩ := st
  apply unifyInduction (P := fun l => _) l <;> intros l <;> simp [StateUnifier, ConstrUnifier] <;> intros
  . grind
  . simp at l
  case _ x t _ _ _ _ =>
    simp [unifyStep]
    have h' := varUnifyNotSome x t σ (by trivial)
    apply isSomeBindSome; trivial
    grind
  case _ x t _ _ _ h _ =>
    simp [unifyStep]
  . simp [Unifier, apply] at *; simp [unifyStep]; trivial
  . simp [Unifier, apply] at *; simp [unifyStep]

#check substCodom

lemma varSubstVars x (t u : Term) : (u.apply (varSubst x t)).vars ⊆ t.vars ∪ (u.vars \ {x}) := by
    apply substCodom; intros y h
    by_cases h':(y = x) <;> simp [h', vars]
    grind

lemma substConstrUnion x t l : constrVars ((varSubst x t).map₂ l) ⊆ t.vars ∪ constrVars l := by
  induction l <;> simp [constrVars, Subst.map₂]
  case cons hd tl ih =>
    let ⟨u₁, u₂⟩ := hd
    simp
    have h₁ := varSubstVars x t u₁
    have h₂ := varSubstVars x t u₂
    apply Finset.union_subset
    . grind
    . apply Finset.union_subset
      . grind
      . have h' : -- hmpf
         constrVars (List.map (fun x_1 => (x_1.1.apply (varSubst x t), x_1.2.apply (varSubst x t))) tl) =
         constrVars ((varSubst x t).map₂ tl) := by eq_refl
        rw [h']
        grind


lemma disjSubst (t u : Term) (h : Disjoint S t.vars) (h' : Disjoint S u.vars)
 : Disjoint S (u.apply (varSubst x t)).vars := by
  have h₂ : (u.apply (varSubst x t)).vars ⊆ u.vars ∪ t.vars := by
    apply substCodom; intros y h
    by_cases h':(y = x) <;> simp [h', vars]
    grind
  apply Disjoint.mono_right (c := u.vars ∪ t.vars); trivial
  apply Disjoint.sup_right <;> trivial

@[grind →]
lemma unifyStepVarCases (t : Term) (h : unifyStep ⟨τ, (var x, t)::l⟩ |>.isSome) :
  t = var x ∨ x ∉ t.vars := by
  have h' := varUnify_some_iff x t
  simp [unifyStep] at h
  cases h'':(varUnify x t) <;> simp [h''] at h
  simp [h''] at h'
  grind

lemma disjointVarSubst (x : Var) (t u : Term) (h : x ∉ t.vars)
 : Disjoint {x} (u.apply (varSubst x t)).vars := by
  induction u <;> simp [apply, vars]
  case _ y =>
    by_cases h':(y = x) <;> simp [h', vars] <;> grind
  case _ => simp at *; grind

lemma disjointConstrVarSubst {x : Var} {t : Term} (h : x ∉ t.vars)
 : Disjoint {x} (constrVars <| (varSubst x t).map₂ l) := by
  induction l <;> simp [Subst.map₂, constrVars]
  case _ _ ih =>
  have h' := disjointVarSubst (x := x) t
  simp at *
  constructor; grind
  constructor; grind
  apply ih


theorem unifyDisj (st : UnifyState) (h : unifyStep st |>.isSome)
  : ConstrDisjVar st → ConstrDisjVar (unifyStep st |>.get h) := by
  revert h
  let ⟨τ, l⟩ := st
  apply unifyInduction (P := fun l => _) l
  . grind
  . intros h; simp [unifyStep] at h
  . intros l x t dummy h; clear dummy
    simp [unifyStep, ConstrDisjVar, constrVars, vars]
    intros
    cases (unifyStepVarCases _ h)
    case _ isVar =>
      simp [isVar]
      trivial
    case _ =>
      apply Disjoint.mono_left (b:= (τ.dom ∪ {x}))
      . have h := scompDom τ (varSubst x t)
        have h' := varSubstDom x t
        simp; grind -- This one is a bit awkard to grind
      . simp; constructor
        . have h' := disjointConstrVarSubst (x:=x) (t:=t) (l:=l)
          simp at h'; grind
        . apply Disjoint.mono_right (c:= ↑(t.vars ∪ constrVars l))
          . apply substConstrUnion -- miracle
          . simp; grind
  . intros l x t nvar dummy h; clear dummy
    simp [unifyStep, ConstrDisjVar, constrVars, vars]
  . intros _ _ _ _ _; simp [ConstrDisjVar, unifyStep, constrVars, vars]
  . intros _ _ _ _ _; simp [ConstrDisjVar, unifyStep, constrVars, vars]
    grind

-- For some reason, an essential trick is the idempotence of the constructed thing:
def Subst.Idem (σ : Subst) := σ.scomp σ = σ

@[simp]
lemma Subst.IdemApp (σ : Subst) (h : σ.Idem) (t : Term) :
  (t.apply σ).apply σ = t.apply σ := by
  simp [Subst.Idem] at h
  have h' : (t.apply σ).apply σ = t.apply (σ.scomp σ) := by simp
  grind

@[simp]
lemma Subst.IdemVar (σ : Subst) (h : σ.Idem) (x : Var) :
  (σ x).apply σ = σ x := by
  have h' := Subst.IdemApp σ h (var x)
  simp [apply] at h'
  trivial

abbrev IdemState (st : UnifyState) := st.subst.Idem ∧ ConstrDisjVar st

-- A sufficient (and necessary, but whatever) condition for being idempotent:
def Subst.IdemAux (σ : Subst) := ∀ x, Disjoint σ.dom (σ x).vars

lemma idemAuxToIdem (σ : Subst) : σ.IdemAux → σ.Idem := by
  simp [IdemAux, Idem]; intros; funext y
  apply varDom; grind

lemma substVarIdem x t (h : x ∉ t.vars) : (varSubst x t).Idem := by
  apply idemAuxToIdem; intros y
  have h' := varSubstDom x t
  by_cases h'' : (y = x) <;> simp [h'', vars] <;> grind


lemma substIdOnVars (σ : Subst) (t : Term) (h : t.apply σ = t)
  : ∀ x ∈ t.vars, σ x = var x := by
  induction t <;> simp [vars, apply] at * <;> grind

@[simp]
lemma idemSubstApplyVAr (σ : Subst) (h : σ.Idem) x
  : (σ x).apply σ = σ x := by rw [← scomp, h]

lemma idemToIdemAux (σ : Subst) : σ.Idem → σ.IdemAux := by
  simp [IdemAux]; intros h x
  have h : ∀ y ∈ ↑(σ x).vars, y ∉ σ.dom := by
    intros y h'
    have h'' := substIdOnVars σ (σ x) (by simp [h]) _ h'
    simp [dom]; trivial
  grind

lemma idemIdemAuxIff (σ : Subst) : σ.Idem ↔ σ.IdemAux := by
  grind [idemToIdemAux, idemAuxToIdem]

#check scompDom
#check varSubstVars

lemma idemScomp (σ : Subst) (x : Var) (t : Term)
  (h₁ : σ.Idem)
  (h₂ : x ∉ t.vars)
  (h₃ : Disjoint σ.dom t.vars)
  : σ.scomp (varSubst x t) |>.Idem := by
  rw [idemIdemAuxIff] at *
  simp [IdemAux, scomp]; intros y
  apply Disjoint.mono_left (b := σ.dom ∪ {x})
  . have h := scompDom σ (varSubst x t)
    have h' := varSubstDom x t
    simp; grind
  . apply Disjoint.mono_right (c := ↑(t.vars ∪ ((σ y).vars \ {x})))
    . apply varSubstVars x t (σ y)
    . simp
      simp [IdemAux] at h₁
      grind

theorem unifyStepIdem (st : UnifyState) (h : unifyStep st |>.isSome)
  : IdemState st → IdemState (unifyStep st |>.get h) := by
  intros idemSt
  have disjConstr : ConstrDisjVar ((unifyStep st).get h) := by
    apply unifyDisj; apply idemSt.2
  simp [IdemState]; refine (And.intro ?X (by trivial))
  revert idemSt h
  let ⟨τ, l⟩ := st
  apply unifyInduction (P := fun l => _) l
  . grind
  . simp [unifyStep]
  . intros l x t discard isSome idemSt; clear discard
    simp [unifyStep]; intros disj
    by_cases h: (t = var x); simp [h]; apply idemSt.1
    apply idemScomp
    . apply idemSt.1
    . grind
    . have h := idemSt.2
      simp [ConstrDisjVar, constrVars] at h
      grind
  . intros l x t _ discard isSome idemSt; clear discard
    simp [unifyStep]; intros; grind
  . simp [unifyStep]; intros; trivial
  . simp [unifyStep]; intros; trivial

#check WellFounded.induction

lemma unify_auxUnifyStepIsSome (st : UnifyState)
  (nNil : ¬ st.constraints.isEmpty)
  (nNone : unify_aux st |>.isSome)
  : unifyStep st |>.isSome := by
  let ⟨τ, constr⟩ := st
  cases constr
  . simp at nNil
  case _ head tail =>
    unfold unify_aux at nNone
    simp at nNone
    cases h:(unifyStep ⟨τ, head::tail⟩)
    . simp [h] at nNone
    . trivial

-- Maybe I don't need to prove this?
lemma unifyFunInd (P : UnifyState → Prop)
  (st : UnifyState)
  (start : P st)
  (step : ∀ st (h : unifyStep st |>.isSome), P st → P (unifyStep st |>.get h))
  (h : unify_aux st |>.isSome)
   : P (unify_aux st |>.get h) := by
  unfold unify_aux
  let ⟨τ, constr⟩ := st
  cases constr <;> simp; trivial
  case _ head tail =>
    have stepSome := unify_auxUnifyStepIsSome ⟨τ, head::tail⟩ (by simp) h
    simp [stepSome]
    apply unifyFunInd
    . apply step
      trivial
    . grind
  termination_by ltState st
  decreasing_by
    have h := decltState (st:=⟨τ, constr⟩) (h:= by grind)
    grind

lemma unifyFunIndBack (P : UnifyState → Prop)
  (st : UnifyState)
  (h : unify_aux st |>.isSome)
  (ending : P (unify_aux st |>.get h))
  (step : ∀ st (h : unifyStep st |>.isSome), P (unifyStep st |>.get h) → P st)
   : P st := by
  let ⟨τ, constr⟩ := st
  unfold unify_aux at ending
  cases constr <;> simp at ending; trivial
  case _ head tail =>
    have stepSome := unify_auxUnifyStepIsSome ⟨τ, head::tail⟩ (by simp) h
    simp [stepSome] at ending
    apply step
    . apply unifyFunIndBack
      . apply ending -- what's happening here?
      . trivial
  termination_by ltState st
  decreasing_by
    have h := decltState (st:=⟨τ, constr⟩) (h:= by grind)
    grind

-- God I hate this lemma. Basically we're traveling both forward and backwards to our
-- destination. Forward for the Q's and backword for the P's.
lemma unifyFunIndBi
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
  cases constr <;> simp at ending; trivial
  case _ head tail =>
    have stepSome := unify_auxUnifyStepIsSome ⟨τ, head::tail⟩ (by simp) h
    simp [stepSome] at ending
    have h : Q ⟨τ, head::tail⟩ := by trivial
    apply stepBack ⟨τ, head::tail⟩ (by grind) h _
    . apply unifyFunIndBi (Q := Q) (st := (unifyStep { subst := τ, constraints := head :: tail }).get (by trivial))
      . apply stepForth; trivial
      . trivial
      . apply ending
      . trivial
  termination_by ltState st
  decreasing_by
    have h := decltState (st:=⟨τ, constr⟩) (h:= by grind)
    grind


-- Ok now we're ready to prove actual soundness and completeness of the unification process.

#print StateUnifier

lemma unify_auxComplete
  (unif : StateUnifier σ st)
  (h : unify_aux st |>.isSome)
   : StateUnifier σ (unify_aux st |>.get h) := by
  apply unifyFunInd <;> grind [unifyStepComplete]

lemma unify_auxIdem
  (unif : IdemState st)
  (h : unify_aux st |>.isSome)
   : IdemState (unify_aux st |>.get h) := by
  apply unifyFunInd <;> grind [unifyStepIdem]

@[simp]
lemma unify_auxEmptyConstr
  (h : unify_aux st |>.isSome)
  : (unify_aux st |>.get h).constraints = [] := by
  let ⟨τ, l⟩ := st
  cases l
  . simp [unify_aux]
  case _ head tail =>
    unfold unify_aux
    simp
    have stepSome := unify_auxUnifyStepIsSome ⟨τ, head::tail⟩ (by simp) h
    simp [stepSome]
    apply unify_auxEmptyConstr
  termination_by ltState st
  decreasing_by
    have h := decltState (st:=⟨τ, l⟩) (h:= by grind)
    grind


lemma unify_auxEnding
  (unif : IdemState st)
  (h : unify_aux st |>.isSome)
  : StateUnifier (unify_aux st |>.get h).subst (unify_aux st |>.get h) := by
  simp [StateUnifier, ConstrUnifier, SubstUnifier]
  intros x
  have h' := unify_auxIdem (st:=st) unif h |>.1
  have h'' := Subst.IdemVar (σ := (unify_aux st).get h |>.subst) h' x
  grind

#check unifyStepComplete

lemma unify_auxSound
  (unif : IdemState st)
  (h : unify_aux st |>.isSome)
  : StateUnifier (unify_aux st |>.get h).subst st := by
  apply unifyFunIndBi (Q := IdemState) (P := fun st' =>
    StateUnifier (unify_aux st |>.get h).subst st')
  . trivial
  . grind [unifyStepIdem]
  . grind [unify_auxEnding]
  . intros st' h' idemSt unifierUnify
    apply unifyStepSound
    . apply idemSt.2
    . trivial
  . trivial

lemma idemStateId : IdemState ⟨idSubst, l⟩ := by
  simp [IdemState]; constructor <;> simp [Idem, ConstrDisjVar]

theorem unifySound (h : unify t u |>.isSome) : Unifier (unify t u |>.get h) t u := by
  simp [unify]
  simp [unify] at h
  have h' : IdemState ⟨idSubst, [(t, u)]⟩ := by apply idemStateId
  have h'' := unify_auxSound (by trivial) (by trivial)
  simp [StateUnifier, ConstrUnifier] at h''
  grind

theorem unifyComplete_aux
  (unif : StateUnifier σ st)
  (h : unifyStep st |>.isSome)
  : ∃ τ, σ = (unifyStep st |>.get h).subst.scomp τ := by sorry

end Unification

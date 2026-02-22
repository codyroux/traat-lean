import Traat.chapter1
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

-- We're going to define an applicative version of terms.
-- We don't parametrize on vars or signature, a specific
-- countable set should do just fine.

def Var := String
def Sig := String

instance : DecidableEq Var := by simp [Var]; infer_instance
instance : DecidableEq Sig := by simp [Sig]; infer_instance

inductive Term where
| var : Var → Term
| func : Sig → Term
| app : Term → Term → Term
deriving DecidableEq

open Term

instance : Coe String Term where
  coe f := func f

infixl:30 " @@ " => app

-- TODO: have an elaborator for terms, to avoid having ugly `@@`s everywhere.
#check "f" @@ var "x" @@ var "y"

-- Substitutions are just (total) functions from variables
-- to terms.
abbrev Subst := Var → Term

-- The domain of a substitution is the set of variables
-- which are *not* sent to themselves.
def Subst.dom (σ : Subst) : Set Var := { x | σ x ≠ var x }

def Term.apply (t : Term) (σ : Subst) : Term :=
  match t with
  | var v => σ v
  | t₁ @@ t₂ => t₁.apply σ @@ t₂.apply σ
  | _ => t

-- We compose substitutions in the "inverse" order, that is,
-- the opposite of what `∘` does (but the natural order for arrows)
def Subst.scomp (σ : Subst) (τ : Subst) : Subst :=
  fun x => (σ x).apply τ

abbrev Subst.idSubst : Subst := var

#check Finset.disjUnion_eq_union
#check Finset.instUnion

def Term.vars : Term → Finset Var
| var v => {v}
| t₁ @@ t₂ => t₁.vars ∪ t₂.vars
| _ => {}

-- We do occasionally want to talk about the
-- functions that appear in a term.
def Term.sig : Term → Finset Sig
| func f => {f}
| t₁ @@ t₂ => t₁.sig ∪ t₂.sig
| _ => {}

@[grind =_]
lemma Term.subst_id (t : Term) : t = t.apply Subst.idSubst := by induction t <;> grind [Term.apply]

-- Ok let's define equations, and formalize deduction.
section Equational

structure FormalEq where
  lhs : Term
  rhs : Term

infix:29 " ≅ " => FormalEq.mk

#check "f" @@ var "x" ≅ "g" @@ var "x"

open Subst

-- Sometimes it's useful to not have variables
-- in application position
def Term.headApp : Term → Sig ⊕ Var
| var v => Sum.inr v
| func f => Sum.inl f
| t₁ @@ _ => headApp t₁

def Term.firstorder : Term → Bool
| var _ => true
| func _ => true
| t₁ @@ t₂ => t₁.headApp.isLeft && t₁.firstorder && t₂.firstorder

-- And sometimes we want more: that a function is applied to some exact number
-- of arguments.

def Arity := Sig → ℕ

def respectArity_N (a : Arity) (n : ℕ) (t : Term) : Bool :=
match t with
| var _ => n = 0
| func f => n = a f
| t₁ @@ t₂ => respectArity_N a (n+1) t₁ && respectArity_N a 0 t₂

def Term.respectArity (a : Arity) (t : Term) := respectArity_N a 0 t

#eval Term.respectArity (fun f => if f = "f" then 2 else if f = "g" then 1 else 0) ("f" @@ ("g" @@ var "x") @@ (var "y"))

#eval Term.respectArity (fun f => if f = "f" then 2 else if f = "g" then 1 else 0) ("f" @@ ("g" @@ var "x"))

abbrev Ctxt := Set FormalEq

set_option hygiene false
infix:25 " ⊢ " => Derives

-- The classic theory of equational logic. This underlies
-- pretty much all of rewrite theory.
@[grind]
inductive Derives : Ctxt → FormalEq → Prop where
| ax : (t ≅ u) ∈ Γ → Γ ⊢ t ≅ u
| refl : Γ ⊢ (t ≅ t)
| symm : Γ ⊢ (t ≅ u) → Γ ⊢ (u ≅ t)
| trans : Γ ⊢ (t ≅ u) → Γ ⊢ (u ≅ v) → Γ ⊢ (t ≅ v)
| congr : Γ ⊢ t₁ ≅ t₂ → Γ ⊢ u₁ ≅ u₂ → Γ ⊢ t₁ @@ u₁ ≅ t₂ @@ u₂
| subst : Γ ⊢ (t ≅ u) → Γ ⊢ (t.apply σ ≅ u.apply σ)

#check {} ⊢ "f" @@ var "x" ≅ "f" @@ var "x"

-- At the moment, there are a lot of "junk theorems", since we are untyped, and
-- in an applicative framework. Nevertheless, the completness theorem holds.

abbrev Valuation (ℳ : Type) := Var → ℳ

abbrev Interp (ℳ : Type) := Sig → ℳ

abbrev App (ℳ : Type) := ℳ → ℳ → ℳ

class Model (ℳ : Type) where
  interp : Interp ℳ
  app : App ℳ

def Term.eval [M : Model ℳ] (t : Term) (θ : Valuation ℳ) : ℳ :=
match t with
| var v => θ v
| func f => M.interp f
| t₁ @@ t₂ => M.app (eval t₁ θ) (eval t₂ θ)


#check ⟦3⟧
#check Quotient.mk


-- I guess ⟦ _ ⟧ is taken? Not sure how to overload
notation "⦃" t:30 "⦄" => Term.eval t

-- What a little annoying in the applicative space is that we now need to
-- build our domains as disjoint sums of function spaces, mostly.

abbrev ExampleDom := ℕ ⊕ (ℕ → ℕ) ⊕ (ℕ → ℕ → ℕ)

instance ExampleModel : Model ExampleDom where
  interp f :=
    match f with
    | "+" => Sum.inr (Sum.inr Nat.add)
    | "×" => Sum.inr (Sum.inr Nat.add)
    | "S" => Sum.inr (Sum.inl Nat.succ)
    | "0" => Sum.inl 0
    | _ => Sum.inl 0
  app f x :=
    match f, x with
    | Sum.inr (Sum.inr f), Sum.inl n => Sum.inr (Sum.inl <| f n)
    | Sum.inr (Sum.inl f), Sum.inl n => Sum.inl <| f n
    | _, _ => Sum.inl 0

#check ⦃"+" @@ ("S" @@ "0") @@ "0"⦄ (fun _ => Sum.inl 0 : Valuation ExampleDom)
#eval ⦃"+" @@ ("S" @@ "0") @@ ("S" @@ var "x")⦄ (fun _ => Sum.inl 0 : Valuation ExampleDom) |>.getLeft?

@[simp]
def FormalEq.eval [M : Model ℳ] (E : FormalEq) (θ : Valuation ℳ) : Prop := ⦃E.lhs⦄ θ = ⦃E.rhs⦄ θ

@[simp]
def FormalEq.satisfies (M : Model ℳ) (E : FormalEq) : Prop :=
  ∀ θ : Valuation ℳ, E.eval θ

@[simp]
def Ctxt.satisfies (M : Model ℳ) (Γ : Ctxt) : Prop :=
  ∀ E ∈ Γ, E.satisfies M

@[simp]
def Model.models (M : Model ℳ) (Γ : Ctxt) (E : FormalEq) : Prop :=
  Γ.satisfies M → E.satisfies M

@[simp]
def models (Γ : Ctxt) (E : FormalEq) : Prop :=
  ∀ ℳ [M : Model ℳ], M.models Γ E

infix:25 " ⊧ " => models

#check {} ⊧ "f" @@ var "x" ≅ "f" @@ var "x"

example : {} ⊧ "f" @@ var "x" ≅ "f" @@ var "x" := by simp

lemma subst_eval [M : Model ℳ] (θ : Valuation ℳ) σ t : ⦃t.apply σ⦄ θ = ⦃t⦄ (fun x => ⦃σ x⦄ θ) := by
  induction t <;> simp [Term.apply, Term.eval]
  case _ => grind

theorem soundness : Γ ⊢ E → Γ ⊧ E := by
  intros h; induction h
  case _ t u h =>
    simp; intros _ _ h' θ
    apply h' ⟨t, u⟩; trivial
  case _ => simp only [models, Model.models, Ctxt.satisfies, FormalEq.satisfies, FormalEq.eval,
    implies_true]
  case _ h' =>
    simp only [models, Model.models, Ctxt.satisfies, FormalEq.satisfies, FormalEq.eval]; intros; symm
    apply h'; trivial
  case _ t u v h₁ h₂ h₃ h₄ =>
    simp only [models, Model.models, Ctxt.satisfies, FormalEq.satisfies, FormalEq.eval]; intros _ _ θ _
    trans
    . apply h₃; trivial
    . apply h₄; trivial
  case _ _ _ _ _ _ _ h₁ h₂ =>
    simp only [models, Model.models, Ctxt.satisfies, FormalEq.satisfies, FormalEq.eval, eval]; intros
    rw [h₁, h₂] <;> trivial
  case _ t u σ _ h =>
    simp only [models, Model.models, Ctxt.satisfies, FormalEq.satisfies, FormalEq.eval] at h; simp
    intros _ _ _ θ
    let θ' := fun x => ⦃σ x⦄ θ
    have h := h _ (by trivial) θ'
    rewrite [subst_eval]; rewrite [subst_eval] -- why does repeat rewrite not work?
    exact h

-- Ok now for completeness. Let's build a little term model.

#check Quotient
#print Setoid
#print Equivalence

def CtxtRel (Γ : Ctxt) (t u : Term) : Prop := Γ ⊢ t ≅ u

def EqCtxRel Γ : Equivalence (CtxtRel Γ) where
  refl := by grind [CtxtRel]
  symm := by grind [CtxtRel]
  trans := by grind [CtxtRel]

lemma ctxtRelCongr (Γ : Ctxt) (t₁ t₂ u₁ u₂ : Term) :
  CtxtRel Γ t₁ t₂ → CtxtRel Γ u₁ u₂ → CtxtRel Γ (t₁ @@ u₁) (t₂ @@ u₂) := by
  grind [CtxtRel]

instance SetoidCtx (Γ : Ctxt) : Setoid Term where
  r := CtxtRel Γ
  iseqv := EqCtxRel Γ

def TermModel (Γ : Ctxt) := Quotient <| SetoidCtx Γ

#check Quotient.map₂'

-- the "term model"
instance ModelSetoidCtx (Γ : Ctxt) : Model (TermModel Γ) where
  interp f := ⟦ func f ⟧
  app t₁ t₂ := Quotient.map₂ (· @@ ·) (by intros; apply ctxtRelCongr <;> trivial) t₁ t₂

#check Quotient.eq_iff_equiv

lemma subst_term_model (Γ : Ctxt) (t : Term) (σ : Subst) :
  let t_σ : TermModel Γ := ⟦t.apply σ⟧
  let t_θ : TermModel Γ := ⦃ t ⦄ (fun x => ⟦σ x⟧)
  t_σ = t_θ := by
  simp; induction t <;> simp [eval, Term.apply]
  case _ => eq_refl
  case _ _ _ ih₁ ih₂ =>
    rw [← ih₁, ← ih₂]
    simp only [Model.app, Quotient.map₂_mk]

#check Quotient.out
#check Quotient.out_eq

lemma subst_lift (Γ : Ctxt) (t : Term) (θ : Valuation (TermModel Γ)) :
  let lift_θ : Subst := fun x => (θ x).out
  ⟦ t.apply lift_θ ⟧ = ⦃ t ⦄ θ := by
  simp; rw [subst_term_model]; congr
  funext; simp

theorem completeness (Γ : Ctxt) (E : FormalEq) : Γ ⊧ E → Γ ⊢ E := by
  intros models
  have h : (∀ E ∈ Γ, ∀ (θ : Valuation (TermModel Γ)), ⦃E.lhs⦄ θ = ⦃E.rhs⦄ θ) := by
    intros E mem θ
    rw [← subst_lift]; rw [← subst_lift, Quotient.eq_iff_equiv]
    simp [HasEquiv.Equiv, SetoidCtx, CtxtRel]
    apply Derives.subst; apply Derives.ax; exact mem
  have models := models (TermModel Γ) h (fun x => ⟦var x⟧); simp at models
  rw [← subst_term_model] at models
  rw [← subst_term_model, Quotient.eq_iff_equiv, ← subst_id] at models
  rw [← subst_id] at models; exact models

end Equational

-- on to rewriting! Not that different.
section Rewriting

structure Rule where
  lhs : Term
  rhs : Term

abbrev Rules := Set Rule

open Subst
-- This is not quite rewriting logic, since we'll only have
-- congruence and not all the relfexive transitive stuff.
@[grind]
inductive Reduces (ℛ : Rules) : Term → Term → Prop where
| ax : ⟨l, r⟩ ∈ ℛ → Reduces ℛ l r
| congr : Reduces ℛ t₁ t₂ → Reduces ℛ u₁ u₂ → Reduces ℛ (t₁ @@ u₁) (t₂ @@ u₂)
| subst : Reduces ℛ t u → Reduces ℛ (t.apply σ) (u.apply σ)

-- Let's fix a rewrite system
variable (ℛ : Rules)

abbrev RTerm (_ℛ : Rules) := Term

instance termRed : Red (RTerm ℛ) where
  reduces := Reduces ℛ

#check termRed
-- set_option trace.Meta.synthInstance true
#synth Red (RTerm ℛ)

-- This is a little depressing: We can't just use `Term` here to get the notation.
#check fun (t u : RTerm ℛ) => t ~> u

#check let t : RTerm ℛ := "f" @@ var "x"; let u : RTerm ℛ := "g" @@ var "x"; t ~> u

-- Test lemma
lemma Test.idRed (t : RTerm ℛ) : t ~>* t := by simp [Red.reduces]; grind

def Unifier (σ : Subst) (t u : Term) : Prop := t.apply σ = u.apply σ

def Unifies (t u : Term) : Prop := ∃ σ, Unifier σ t u

def varSubst (x : Var) (t : Term) : Subst := fun y => if y = x then t else var y

@[simp]
lemma varSubstNEq (h : y ≠ x) : varSubst x t y = var y := by grind [varSubst]

@[simp]
lemma varSubstEq : varSubst x t x = t := by grind [varSubst]

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

lemma varUnifyMGU  (x : Var) (t : Term) (σ : Subst)
  (unifies : varUnify x t |>.isSome)
  (hasUnifier : σ x = t.apply σ)
: let mgu := varUnify x t |>.get unifies
  ∃ τ : Subst, mgu.scomp τ = σ := by
  simp [varUnify]
  exists (fun y => if y = x then t.apply σ else σ y)
  funext y
  by_cases h:(y = x); simp [h, scomp]
  . rw [substDom t _ σ] <;> grind
  . simp [scomp, h, Term.apply]

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


structure UnifyState where
  subst : Subst
  constraints : List (Term × Term)

def constrVars : List (Term × Term) → Finset Var
| [] => {}
| (t, u) :: cs => t.vars ∪ u.vars ∪ (constrVars cs)

def Subst.map₂ (σ : Subst) (l : List (Term × Term)) : List (Term × Term) :=
  l.map (fun (x, y) => (x.apply σ, y.apply σ))

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

lemma excludeConstrCodom (l : List (Term × Term)) (σ : Subst) (x : Var) (h : ∀ y, x ∉ (σ y).vars) : x ∉ constrVars (σ.map₂ l) := by
  induction l <;> simp [Subst.map₂, constrVars]
  case _ t₁ t₂ ih =>
    have h' := fun t => excludeCodom t σ x h
    exact ⟨h' _, h' _, ih⟩ -- why doesn't grind work here?

def unifyStep (st : UnifyState) : Option UnifyState :=
  match st.constraints with
  | [] => none -- kind of a hack to fail here, but we won't hit this branch.
  | (var x, t) :: cstr => do
    let σ ← varUnify x t
    let newConstr := σ.map₂ cstr
    return ⟨σ.join st.subst, newConstr⟩
  | (t, var x) :: cstr => do
    let σ ← varUnify x t
    let newConstr := cstr.map (fun (x, y) => (x.apply σ, y.apply σ))
    return ⟨σ.join st.subst, newConstr⟩
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

noncomputable def ltState (st : UnifyState) : ℕ × ℕ :=
  (constrVars st.constraints |> Finset.card, constrSize st.constraints)

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

@[simp]
lemma varSubstId (t : Term) : t.apply (varSubst x (var x)) = t := by
  induction t <;> simp [apply, varSubst] <;> grind

@[simp]
lemma varSubstIdMap : (varSubst x (var x)).map₂ l = l := by
  induction l <;> simp [map₂]

-- This is quite a bit more tedious than I'd like.
lemma decltState : Prod.Lex (· < ·) (· < ·)
  (ltState ((unifyStep st).get h)) (ltState st) := by
  have ⟨_, l⟩ := st
  cases l <;> simp [unifyStep]
  case nil => simp [unifyStep] at h
  -- These are just a single deconstruction, there's gotta be a better way.
  case cons hd tail =>
  cases hd
  case _ t u =>
  --------------
  cases t
  case _ x =>
    by_cases (u = var x)
    case _ h' =>
      apply Prod.Lex.right' <;> simp [h']
      . simp [constrVars]
        apply Finset.card_mono
        simp [LE.le]
        grind
      . simp [constrSize]
    case _ =>
      apply Prod.Lex.left; simp [constrVars, Term.vars]
      apply constrRemoveVar <;> grind
  case _ =>
    cases u
    case _ f x =>
      apply Prod.Lex.left; simp [constrVars, Term.vars]
      have h' := constrRemoveVar (x:=x) (tail:=tail) (u := func f)
      simp [Subst.map₂, Term.vars] at h'
      apply h'; simp [varUnify, vars]
    case _ =>
      apply Prod.Lex.right' <;> simp [constrVars]
      . apply Finset.card_mono
        simp [LE.le]; grind
      . simp [constrSize]
    case _ => simp [unifyStep] at h
  case _ t₁ t₂ =>
    cases u
    case _ x =>
      apply Prod.Lex.left; simp [constrVars, Term.vars]
      have h' := constrRemoveVar (x:=x) (tail:=tail) (u := t₁ @@ t₂)
      simp [Subst.map₂, Term.vars] at h'
      apply h'; simp [unifyStep] at h
      cases h'' :(varUnify x (t₁ @@ t₂))
      . rw [h''] at h; simp at h
      . simp
    case _ => simp [unifyStep] at h
    case _ =>
      apply Prod.Lex.right' <;> simp [constrVars]
      . apply Finset.card_mono
        simp [LE.le, Term.vars]; grind
      . simp [constrSize]; grind

def unify_aux (st : UnifyState) : Option Subst :=
  match st.constraints with
  | [] => return st.subst
  | _ =>
    -- We can't use pretty do notation here to not confuse the termination
    -- checker
    let st' := unifyStep st
    if h: st'.isSome then unify_aux (st'.get h) else none
  termination_by ltState st
  decreasing_by
    apply decltState

def unify (t u : Term) : Option Subst := unify_aux ⟨idSubst, [(t, u)]⟩

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

def constrUnifier (σ : Subst) (l : List (Term × Term)) : Prop :=
  match l with
  | [] => True
  | (t, u) :: l' =>
    Unifier σ t u ∧ constrUnifier σ l'

def substUnifier (τ σ : Subst) : Prop := ∀ x, τ x = (σ x).apply τ

def stateUnifier (σ : Subst) (st : UnifyState) : Prop :=
  substUnifier σ st.subst ∧ constrUnifier σ st.constraints


def isUnifyFail (t u : Term) : Bool :=
  match t, u with
  | var _, _
  | _, var _
  | func _, func _
  | _ @@ _, _ @@ _ => false
  | _, _ => true

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
  (unify₂ : constrUnifier σ l)
   : constrUnifier σ ((varSubst x t).map₂ l) := by
  induction l <;> simp [Subst.map₂, constrUnifier]; simp [constrUnifier] at unify₂
  case _ head tl ih =>
  constructor
  . apply unifierVarSubst <;> grind
  . apply ih; grind

theorem unifySound (σ : Subst) (st : UnifyState) (h : unifyStep st |>.isSome) :
  stateUnifier σ st → stateUnifier σ (unifyStep st |>.get h) := by
  let ⟨τ, l⟩ := st
  revert h τ
  apply unifyInduction (P := fun l => _) l
  case _ => intros _ t u; cases t <;> cases u <;> simp [isUnifyFail, unifyStep]
  case _ => simp [unifyStep]
  case _ =>
    intros l x t ih τ h unif; clear ih
    simp [unifyStep, stateUnifier, substUnifier]
    simp [stateUnifier] at unif
    have h' := varSubstDomCases x t
    cases h'
    case _ h' =>
      simp [h']; constructor
      . intros y
        by_cases h'': (y = x) <;> simp [h'']
        . simp [constrUnifier, Unifier, apply] at unif; grind
        . apply unif.1
      . apply constrUnifierVarSubst <;> simp [constrUnifier, Unifier, apply] at unif <;> grind
    case _ h' =>
      simp [h']; constructor
      . apply unif.1
      . apply constrUnifierVarSubst <;> simp [constrUnifier, Unifier, apply] at unif <;> grind
  case _ =>
    intros l x t nvar ih τ h unif; clear ih
    simp [unifyStep, stateUnifier, substUnifier]
    simp [stateUnifier] at unif
    have h' := varSubstDomCases x t
    cases h'
    case _ h' =>
      simp [h']; constructor
      . intros y
        by_cases h'': (y = x) <;> simp [h'']
        . simp [constrUnifier, Unifier, apply] at unif; grind
        . apply unif.1
      . apply constrUnifierVarSubst <;> simp [constrUnifier, Unifier, apply] at unif <;> grind
    case _ h' =>
      simp [h']; constructor
      . apply unif.1
      . apply constrUnifierVarSubst <;> simp [constrUnifier, Unifier, apply] at unif <;> grind
  case _ =>
    intros _ f g _ τ _
    simp [unifyStep, stateUnifier, constrUnifier]
    grind
  case _ =>
    intros _ t₁ t₂ u₁ u₂ discard; clear discard
    intros τ _
    simp [stateUnifier, constrUnifier, unifyStep, Unifier, apply]
    grind


theorem unifyComplete (σ : Subst) (st : UnifyState) (h : unifyStep st |>.isSome) :
  stateUnifier σ (unifyStep st |>.get h) → stateUnifier σ st := by sorry

-- Is this right?
theorem unifyProgress (σ : Subst) (st : UnifyState) : stateUnifier σ st → (unifyStep st |>.isSome) := by sorry

end Rewriting

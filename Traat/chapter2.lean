import Traat.chapter1
import Mathlib.Data.Finset.Basic

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
def dom (σ : Subst) (x : Var) : Prop := σ x ≠ var x

def Term.apply (t : Term) (σ : Subst) : Term :=
  match t with
  | var v => σ v
  | t₁ @@ t₂ => t₁.apply σ @@ t₂.apply σ
  | _ => t

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

-- Ok let's define equations, and formalize deduction.

structure FormalEq where
  lhs : Term
  rhs : Term

infix:29 " ≅ " => FormalEq.mk

#check "f" @@ var "x" ≅ "g" @@ var "x"


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
| ax : E ∈ Γ → Γ ⊢ E
| refl : Γ ⊢ (t ≅ t)
| symm : Γ ⊢ (t ≅ u) → Γ ⊢ (u ≅ t)
| trans : Γ ⊢ (t ≅ u) → Γ ⊢ (u ≅ v) → Γ ⊢ (t ≅ v)
| inst : Γ ⊢ (t ≅ u) → Γ ⊢ (t.apply σ ≅ u.apply σ)

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
  case _ E h =>
    simp; intros _ _ h' θ
    apply h'; trivial
  case _ => simp
  case _ h' =>
    simp; intros; symm
    apply h'; trivial
  case _ t u v h₁ h₂ h₃ h₄ =>
    simp; intros _ _ θ _
    trans
    . apply h₃; trivial
    . apply h₄; trivial
  case _ t u σ _ h =>
    simp at h; simp
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
  refl := sorry
  symm := sorry
  trans := sorry

instance SetoidCtx (Γ : Ctxt) : Setoid Term where
  r := CtxtRel Γ
  iseqv := EqCtxRel Γ

def TermModel (Γ : Ctxt) := Quotient <| SetoidCtx Γ

#check Quotient.map₂'

-- the "term model"
instance ModelSetoidCtx (Γ : Ctxt) : Model (TermModel Γ) where
  interp f := ⟦ func f ⟧
  app t₁ t₂ := Quotient.map₂ (· @@ ·) _ t₁ t₂

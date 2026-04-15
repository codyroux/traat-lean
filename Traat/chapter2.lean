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
instance : Repr Var := by simp [Var]; infer_instance
instance : Repr Sig := by simp [Sig]; infer_instance

inductive Term where
| var : Var → Term
| func : Sig → Term
| app : Term → Term → Term
deriving DecidableEq, Repr

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

@[simp]
lemma Subst.scomp_apply (σ τ : Subst) (t : Term)
  : t.apply (σ.scomp τ) = (t.apply σ).apply τ := by
  induction t <;> simp [apply, Subst.scomp]
  grind

abbrev Subst.idSubst : Subst := var

@[grind =_]
lemma Term.apply_idSubst (t : Term) : t = t.apply Subst.idSubst := by induction t <;> grind [Term.apply]

@[simp, grind =]
lemma idSubst_apply (t : Term) : t.apply Subst.idSubst = t := by grind

@[simp, grind =]
lemma scomp_idSubst (σ : Subst) : σ.scomp Subst.idSubst = σ := by
  funext; simp [Subst.scomp]

@[simp, grind =]
lemma idSubst_scomp (σ : Subst) : Subst.idSubst.scomp σ = σ := by
  funext; simp [Subst.scomp, apply]


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

def Term.isVar : Term → Bool
| var _ => true
| _ => false


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

lemma eval_apply [M : Model ℳ] (θ : Valuation ℳ) σ t : ⦃t.apply σ⦄ θ = ⦃t⦄ (fun x => ⦃σ x⦄ θ) := by
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
    rewrite [eval_apply]; rewrite [eval_apply] -- why does repeat rewrite not work?
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

lemma CtxtRel.congr (Γ : Ctxt) (t₁ t₂ u₁ u₂ : Term) :
  CtxtRel Γ t₁ t₂ → CtxtRel Γ u₁ u₂ → CtxtRel Γ (t₁ @@ u₁) (t₂ @@ u₂) := by
  grind [CtxtRel]

instance SetoidCtx (Γ : Ctxt) : Setoid Term where
  r := CtxtRel Γ
  iseqv := EqCtxRel Γ

@[reducible]
def TermModel (Γ : Ctxt) := Quotient <| SetoidCtx Γ

#check Quotient.map₂'

-- the "term model"
instance ModelSetoidCtx (Γ : Ctxt) : Model (TermModel Γ) where
  interp f := ⟦ func f ⟧
  app t₁ t₂ := Quotient.map₂ (· @@ ·) (by intros; apply CtxtRel.congr <;> trivial) t₁ t₂

#check Quotient.eq_iff_equiv

lemma Term.apply_termModel (Γ : Ctxt) (t : Term) (σ : Subst) :
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

lemma Term.lift_apply (Γ : Ctxt) (t : Term) (θ : Valuation (TermModel Γ)) :
  let lift_θ : Subst := fun x => (θ x).out
  ⟦ t.apply lift_θ ⟧ = ⦃ t ⦄ θ := by
  simp; rw [Term.apply_termModel]; congr
  funext; simp

#print TermModel

theorem completeness (Γ : Ctxt) (E : FormalEq) : Γ ⊧ E → Γ ⊢ E := by
  intros models
  have h : (∀ E ∈ Γ, ∀ (θ : Valuation (TermModel Γ)), ⦃E.lhs⦄ θ = ⦃E.rhs⦄ θ) := by
    intros E mem θ
    rw [← Term.lift_apply]; rw [← Term.lift_apply, Quotient.eq_iff_equiv]
    simp [HasEquiv.Equiv]
    apply Derives.subst; apply Derives.ax; exact mem
  have models := models (TermModel Γ) h (fun x => ⟦var x⟧); simp at models
  rw [← Term.apply_termModel] at models
  rw [← Term.apply_termModel, Quotient.eq_iff_equiv, ← apply_idSubst] at models
  rw [← apply_idSubst] at models; exact models

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
| head : ⟨l, r⟩ ∈ ℛ → Reduces ℛ (l.apply σ) (r.apply σ)
| congrLeft : Reduces ℛ t₁ t₂ → Reduces ℛ (t₁ @@ u) (t₂ @@ u)
| congrRight : Reduces ℛ u₁ u₂ → Reduces ℛ (t @@ u₁) (t @@ u₂)

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

#print Ctxt
#print Rules
#print Reduces

#check Set.image

def EToR (Γ : Ctxt) : Rules := (fun e => ⟨e.lhs, e.rhs⟩)'' Γ
def RToE (ℛ : Rules) : Ctxt := (fun e => ⟨e.lhs, e.rhs⟩)'' ℛ

@[simp]
def RTerm.apply {ℛ : Rules} (t : RTerm ℛ) (σ : Subst) : RTerm ℛ := Term.apply t σ

lemma Reduces.apply {ℛ : Rules} {t u : RTerm ℛ} (σ : Subst) (red : t ~> u)
 : t.apply σ ~> u.apply σ := by
  simp [Red.reduces] at red; induction red <;> simp [apply]
  case _ l r τ mem =>
   rw [← Subst.scomp_apply]; rw [← Subst.scomp_apply]
   exact Reduces.head (ℛ := ℛ) (l:=l) (r:=r) (σ := τ.scomp σ) mem
  case _ => apply Reduces.congrLeft; trivial
  case _ => apply Reduces.congrRight; trivial

lemma Reduces.refl_trans_clos_apply {ℛ : Rules} (t u : RTerm ℛ) (red : t ~>* u)
 : t.apply σ ~>* u.apply σ := by
  induction red
  case _ => constructor
  case _ a b c red red' ih =>
    have h := Reduces.apply σ red
    grind

lemma Reduces.refl_trans_sym_clos_apply {ℛ : Rules} (t u : RTerm ℛ) (red : t <~>* u)
 : t.apply σ <~>* u.apply σ := by
  induction red
  case _ => constructor
  case _ =>
    apply refl_trans_sym_clos.base
    apply Reduces.apply; trivial
  case _ _ b _ _ _ ih₁ ih₂ =>
    apply refl_trans_sym_clos.trans (b:=b.apply σ)
    . apply ih₁
    . apply ih₂
  case _ _ _ ih =>
    apply refl_trans_sym_clos.inv
    apply ih

def RTerm.app {ℛ} (t₁ t₂ : RTerm ℛ) : RTerm ℛ := t₁ @@ t₂

infix:30 " @@@ " => RTerm.app

-- TODO: do the `~>*` versions also
lemma Reduces.refl_trans_clos_congr_left {ℛ : Rules}
 (t₁ t₂ u : RTerm ℛ)
 (red : t₁ ~>* t₂)
 : (t₁ @@@ u) ~>* (t₂ @@@ u) := by
  induction red
  case _ => constructor
  case _ =>
    apply refl_trans_clos.step; constructor; trivial
    trivial

lemma Reduces.refl_trans_clos_congr_right {ℛ : Rules}
 (t u₁ u₂ : RTerm ℛ)
 (red : u₁ ~>* u₂)
 : (t @@@ u₁) ~>* (t @@@ u₂) := by
  induction red
  case _ => constructor
  case _ =>
    apply refl_trans_clos.step; apply Reduces.congrRight <;> trivial
    trivial

lemma Reduces.refl_trans_clos_congr {ℛ : Rules}
 (t₁ t₂ u₁ u₂ : RTerm ℛ)
 (red₁ : t₁ ~>* t₂)
 (red₂ : u₁ ~>* u₂)
 : (t₁ @@@ u₁) ~>* (t₂ @@@ u₂) := by
  apply refl_trans_clos_trans (y := t₂ @@@ u₁)
  . apply Reduces.refl_trans_clos_congr_left; grind
  . apply Reduces.refl_trans_clos_congr_right; grind

lemma Reduces.refl_trans_sym_clos_congr_left {ℛ : Rules}
 (t₁ t₂ u : RTerm ℛ)
 (red : t₁ <~>* t₂)
 : (t₁ @@@ u) <~>* (t₂ @@@ u) := by
  induction red
  case _ => constructor
  case _ =>
    apply refl_trans_sym_clos.base; constructor; trivial
  case _ ih₁ ih₂ =>
    apply refl_trans_sym_clos.trans
    . apply ih₁
    . apply ih₂
  case _ ih => apply refl_trans_sym_clos.inv; apply ih

lemma Reduces.refl_trans_sym_clos_congr_right {ℛ : Rules}
 (t u₁ u₂ : RTerm ℛ)
 (red : u₁ <~>* u₂)
 : (t @@@ u₁) <~>* (t @@@ u₂) := by
  induction red
  case _ => constructor
  case _ =>
    apply refl_trans_sym_clos.base; constructor; trivial
  case _ ih₁ ih₂ =>
    apply refl_trans_sym_clos.trans
    . apply ih₁
    . apply ih₂
  case _ ih => apply refl_trans_sym_clos.inv; apply ih

lemma Reduces.refl_trans_sym_clos_congr {ℛ : Rules}
 (t₁ t₂ u₁ u₂ : RTerm ℛ)
 (red₁ : t₁ <~>* t₂)
 (red₂ : u₁ <~>* u₂)
 : (t₁ @@@ u₁) <~>* (t₂ @@@ u₂) := by
  apply refl_trans_sym_clos.trans (b := t₂ @@@ u₁)
  . apply Reduces.refl_trans_sym_clos_congr_left; grind
  . apply Reduces.refl_trans_sym_clos_congr_right; grind

lemma derives_of_reduces (ℛ : Rules) (t u : RTerm ℛ) (red : t ~> u) : RToE ℛ ⊢ t ≅ u := by
  simp [Red.reduces] at red; induction red
  case _ l r _ mem =>
    apply Derives.subst; constructor
    simp [RToE]
    exists ⟨l, r⟩
  case _ => apply Derives.congr <;> grind
  case _ => apply Derives.congr <;> grind

theorem derives_of_refl_trans_clos (ℛ : Rules) (t u : RTerm ℛ) (red : t ~>* u) : RToE ℛ ⊢ t ≅ u := by
  induction red
  case _ => grind
  case _ a b c red red' ih =>
    have h : RToE ℛ ⊢ a ≅ b := by
      apply derives_of_reduces; grind
    grind

#print Red
#print Reduces

theorem refl_trans_sym_clos_of_derives_aux (Γ : Ctxt) (eqProof : Γ ⊢ E) :
  refl_trans_sym_clos (Reduces (EToR Γ)) E.lhs E.rhs := by
  induction eqProof
  case _ t u mem =>
    apply refl_trans_sym_clos.base
    rw [← idSubst_apply (t:=t), ← idSubst_apply (t:=u)]
    apply Reduces.head
    simp [EToR]; exists ⟨t, u⟩
  case _ => apply refl_trans_sym_clos.refl
  case _ _ _ _ ih =>
    apply refl_trans_sym_clos.inv; simp
    grind
  case _ =>
    apply refl_trans_sym_clos.trans <;> simp at * <;> trivial
  case _ =>
    simp at *
    apply Reduces.refl_trans_sym_clos_congr <;> trivial
  case _ =>
    simp at *
    apply Reduces.refl_trans_sym_clos_apply
    trivial

theorem refl_trans_sym_clos_of_derives (Γ : Ctxt) (t u : RTerm (EToR Γ)) (eqProof : Γ ⊢ t ≅ u) : t <~>* u := by
  simp [Red.reduces]
  apply refl_trans_sym_clos_of_derives_aux (E := ⟨t, u⟩); grind

end Rewriting

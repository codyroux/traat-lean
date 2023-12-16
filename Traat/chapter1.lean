import Mathlib.Logic.Function.Iterate


section variable {A : Type}

section variable (R : A -> A -> Prop)

#check R

section variable [inhabited_A : Nonempty A]

-- These are a little ad-hoc but they'll serve

inductive trans_clos (R : A -> A -> Prop) : A -> A -> Prop
| base : forall a b, R a b -> trans_clos R a b
| step : forall a b c, R a b -> trans_clos R b c -> trans_clos R a c

inductive refl_clos (R  : A -> A -> Prop) : A -> A -> Prop where
| refl : forall a, refl_clos R a a
| base : forall a b, R a b -> refl_clos R a b

def refl_trans_clos (R  : A -> A -> Prop) : A -> A -> Prop := refl_clos (trans_clos R)

inductive sym_clos (R  : A -> A -> Prop) : A -> A -> Prop
| base : forall a b, R a b -> sym_clos R a b
| inv : forall a b, R b a -> sym_clos R a b

-- The order matters here! Symmetric closure of the symmetric closure
-- is bigger than the symmetric closure of the transitive closure!
def refl_sym_trans_clos (R  : A -> A -> Prop) : A -> A -> Prop :=
 refl_clos (trans_clos (sym_clos R))



set_option quotPrecheck false
infixl:50 " ~> " => R

infixl:50 " ~>+ "   => trans_clos R
infixl:50 " ~>* "   => refl_trans_clos R
infixl:50 " <~>* "  => refl_sym_trans_clos R


def diverge_from (x : A) : Prop :=
  ∃ xs : Nat -> A, xs 0 = x ∧ ∀ n, xs n ~> xs (n+1)

def normalizes (x : A) : Prop := ¬ (diverge_from R x)

def normalizing : Prop := ∀ x : A, normalizes R x

def normal (x : A) : Prop := ¬ (∃ x', x ~> x')

-- Fixme: do better!
theorem normal_normalizing (x : A) : normal R x -> normalizes R x :=
by
  simp [normal]
  intros norm_x div_x
  match div_x with
    | Exists.intro xs (And.intro zero_case incr_case) =>
    apply norm_x (xs 1)
    rw [←zero_case]
    apply incr_case


#check forall_and


theorem exists_iff : ∀ T (P Q : T -> Prop),
        (∀ t, Q t <-> P t) ->
        (∃ t, P t) ->
        ∃ t, Q t :=
by
  intros T P Q equiv ex_t
  match ex_t with 
   | Exists.intro w h =>
     exists w
     simp [equiv]
     exact h


#print Classical.axiomOfChoice

theorem iterate_left : ∀ {A} (f : A -> A) (n : ℕ) (x : A), f^[n+1] x = f (f^[n] x) :=
by
  intros A f n
  induction' n with n ihn
  . simp [Nat.iterate]
  . simp [Nat.add, Nat.iterate]
    intros x
    apply ihn



-- This is gonna need a clever application of AC!
lemma dependent_choice' : ∀ {A} (Q : A -> A -> Prop) (a : A),
      (∀ a, ∃ b, Q a b) ->
      ∃ f : ℕ -> A, f 0 = a ∧ ∀ n, Q (f n) (f (n+1)) :=
by
  intros A Q a forall_exists_Q
  have choice_aut : ∃ f : A -> A, ∀ x, Q x (f x) :=
  (by
    apply Classical.axiomOfChoice
    exact forall_exists_Q)
  match choice_aut with
   | Exists.intro f h =>
       exists (λ n => f^[n] a)
       apply And.intro
       . simp [Nat.iterate]
       . intros n
         simp
         rw [iterate_left]
         apply h


#print Nonempty
#print Inhabited

-- So tedious!
lemma dependent_choice : ∀ {A}
  (Q : A -> A -> Prop),
  Inhabited A ->
  (∀ a, ∃ b, Q a b) ->
  ∃ f : ℕ -> A, ∀ n, Q (f n) (f (n+1)) :=
by
  intros A Q inhab forall_exists_Q
  have a : A := (by match inhab with | Inhabited.mk a => exact a)
  have h := (dependent_choice' _ a forall_exists_Q)
  match h with
  | Exists.intro f h' =>
    exists f
    apply h'.2

#print Subtype
#print Exists

lemma dependent_choice'' : ∀ (P : A -> Prop)
  (Q : A -> A -> Prop) (a : A),
  P a ->
  (∀ a, P a -> ∃ b, P b ∧ Q a b) ->
  ∃ f : ℕ -> A, f 0 = a ∧ ∀ n, P (f n) ∧ Q (f n) (f (n+1)) :=
by
  intros P Q a pa ex
  have h : ∃ (f : ℕ → {x : A // P x}), f 0 = ⟨a, pa⟩
           ∧ ∀ n, P (f n) ∧ Q (f n) (f (n+1)) :=
  (by
    apply (@dependent_choice' {x : A // P x} (λ p q => P p ∧ Q p q) _)
    intros ap
    match ap with
    | Subtype.mk a' p =>
      simp
      apply And.intro
      . exact p
      . match (ex a' p) with
        | Exists.intro b ⟨pb, qb⟩ =>
        exists (Subtype.mk b pb)
   )
  match h with
  | Exists.intro f ⟨zf, sf⟩ =>
    exists (λ n ↦ (f n).val)
    simp; rw [zf]; simp
    intros n; apply sf


-- -- This is the "real" def of normalization, or at least the
-- -- one that's actually useful. It's equivalent, in fact, but we really
-- -- only need this direction.
lemma normalizes_ind : ∀ P : A -> Prop,
  (∀ x, (∀ y, x ~> y -> P y) -> P x) -> ∀ x, normalizes R x -> P x :=
by
  intros P IH x norm
  apply Classical.byContradiction
  intro h; apply norm
  have h' : ∃ f : ℕ -> A, f 0 = x ∧ ∀ n, ¬ P (f n) ∧ f n ~> f (n+1) :=
  (by
    apply (dependent_choice''  (λ a ↦ ¬ P a))
    . exact h
    . intros a npa 
      apply Classical.byContradiction
      simp; intros p
      apply npa
      apply IH; intros y ry
      apply Classical.byContradiction; intros npy
      apply (p y npy ry)
   )
  rw [diverge_from]
  match h' with
    | Exists.intro xs ⟨P0, P1⟩ =>
      exists xs
      apply And.intro
      . exact P0
      . intros n
        apply (P1 n).2
  


lemma normalizing_ind : ∀ P : A -> Prop,
  (∀ x, (∀ y, x ~> y -> P y) -> P x) -> normalizing R -> ∀ x, P x :=
by
  intros P IH norm x
  apply normalizes_ind
  . apply IH
  . apply norm


-- -- Should be easy!
-- lemma red_ref_trans_clos : ∀ x y z, x ~> y -> refl_trans_clos R y z -> refl_trans_clos R x z :=
-- begin
--   intros x y z,
--   intros red_x_y,
--   intros h,
--   induction h,
--     simp [refl_trans_clos],
--     constructor,
--     constructor,
--     exact red_x_y,
--   simp [refl_trans_clos],
--   apply refl_clos.base,
--   apply trans_clos.step,
--     exact red_x_y,
--   exact h_a_1
-- end

-- lemma normalizing_normal (x : A) : normalizes R x -> ∃ y : A, x ~>* y ∧ normal R y
-- :=
-- begin
--   apply normalizes_ind,
--   intros x h,
--   destruct (_ : decidable (∃ y, x ~> y)),
--     intros h' _,
--     existsi x,
--     split,
--     constructor,
--     exact h',
--   intros h' _,
--   destruct h',
--   simp, intros y red_x_y,
--   destruct (h y red_x_y),
--   simp,
--   intros y' h'',
--   existsi y',
--   split,
--     destruct h'',
--   intros h''' _,
--     apply red_ref_trans_clos,
--     exact red_x_y,
--     exact h''',
--   destruct h'',
--   intros _ i, exact i,
--   apply classical.prop_decidable
-- end

-- -- FIXME: define a notation
-- def joins : ∀ (x y : A), Prop := λ x y, ∃ z : A, x ~>* z ∧ y ~>* z

-- -- FIXME: define a notation
-- def wedge : ∀ (u t v : A), Prop := λ u t v, t ~>* u ∧ t ~>* v

-- def church_rosser := ∀ (x y : A), x <~>* y -> joins R x y

-- def confluent := ∀ (x y z : A), wedge R y x z -> joins R y z

-- def strongly_confluent :=
--   ∀ x y z : A, x ~> y -> x ~> z -> ∃ w, y ~> w ∧ z ~> w

-- def weakly_confluent :=
--   ∀ x y z : A, x ~> y -> x ~> z -> ∃ w, y ~>* w ∧ z ~>* w

-- -- let's relate all of these

-- -- this one is trivial
-- lemma church_rosser_implies_confluent : church_rosser R -> confluent R :=
--   sorry

-- lemma strongly_confluent_implies_confluent : strongly_confluent R -> confluent R :=
--   sorry

-- -- also trivial
-- lemma confluent_implies_weakly_confluent : confluent R -> weakly_confluent R :=
--   sorry

-- -- this one is a little more work
-- lemma confluent_implies_church_rosser : confluent R -> church_rosser R :=
--   sorry

-- -- Uh oh!
-- lemma weakly_confluent_does_not_imply_confluent : ∃ A (R : A -> A -> Prop),
--  weakly_confluent R ∧ ¬ confluent R :=
--  sorry

-- -- but if...
-- lemma newmanns_lemma : normalizing R -> weakly_confluent R -> confluent R :=
--   -- Requires a clever induction on diagrams
--   sorry


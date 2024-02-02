import Mathlib.Logic.Function.Iterate


section variable {A : Type}

section variable (R : A → A → Prop)

#check R

section variable [inhabited_A : Nonempty A]

-- These are a little ad-hoc but they'll serve

inductive trans_clos (R : A → A → Prop) : A → A → Prop
| base : ∀ a b, R a b → trans_clos R a b
| step : ∀ a b c, R a b → trans_clos R b c → trans_clos R a c

inductive refl_clos (R  : A → A → Prop) : A → A → Prop where
| refl : ∀ a, refl_clos R a a
| base : ∀ a b, R a b → refl_clos R a b

inductive sym_clos (R  : A → A → Prop) : A → A → Prop
| base : ∀ a b, R a b → sym_clos R a b
| inv : ∀ a b, R b a → sym_clos R a b

inductive refl_trans_clos (R  : A → A → Prop) : A → A → Prop :=
| refl : ∀ a, refl_trans_clos R a a
| step : ∀ a b c, R a b → refl_trans_clos R b c → refl_trans_clos R a c

inductive refl_trans_sym_clos (R  : A → A → Prop) : A → A → Prop :=
| refl : ∀ a, refl_trans_sym_clos R a a
| base : ∀ a b, R a b → refl_trans_sym_clos R a b
| trans : ∀ a b c, refl_trans_sym_clos R a b →
                       refl_trans_sym_clos R b c →
                       refl_trans_sym_clos R a c
| inv : ∀ a b, refl_trans_sym_clos R b a →
                    refl_trans_sym_clos R a b

set_option quotPrecheck false

infix:60 " ⊆ " => (λ (R R' : A → A → Prop) ↦ ∀ x y, R x y → R' x y)
infix:60 " ≅ " => (λ (R R' : A → A → Prop) ↦ ∀ x y, R x y ↔ R' x y)
postfix:100 " ⁻¹ " => (λ (R : A → A → Prop) ↦ λ x y ↦ R y x)
infixl:50 " ~> " => R

infixl:50 " ~>+ "   => trans_clos R
infixl:50 " ~>* "   => refl_trans_clos R
infixl:50 " <~>* "  => refl_trans_sym_clos R

lemma both_inclusions : ∀ (R R' : A → A → Prop),
  R ⊆ R' → R' ⊆ R → R ≅ R' :=
  by
    intros R R' le_1 le_2 x y
    constructor
    . apply le_1
    . apply le_2

lemma trans_clos_monotone : ∀ (R R' : A → A → Prop),
 R ⊆ R' →  trans_clos R ⊆ trans_clos R' :=
  by
    intros R R' le x y tr
    induction tr
    . constructor
      apply le; trivial
    . apply trans_clos.step
      . apply le
        trivial
      . trivial

lemma sym_clos_monotone : ∀ (R R' : A → A → Prop),
 R ⊆ R' →  sym_clos R ⊆ sym_clos R' :=
   by
    intros R R' le x y sym
    induction sym
    . constructor; apply le; trivial
    . apply sym_clos.inv
      apply le; trivial

lemma refl_clos_monotone : ∀ (R R' : A → A → Prop),
 R ⊆ R' →  refl_clos R ⊆ refl_clos R' :=
  by
    intros R R' le x y refl
    induction refl
    . constructor
    . apply refl_clos.base
      apply le; trivial

lemma trans_clos_transitive : ∀ (R : A → A → Prop) x y z,
  trans_clos R x y → trans_clos R y z → trans_clos R x z :=
  by
    intros R x y z tr_x_y
    induction' tr_x_y with _ _ _ _ _ _ _ _ ih
    . intros rest
      apply trans_clos.step <;> trivial
    . intros rest
      apply trans_clos.step; trivial
      apply ih; trivial

lemma refl_trans_clos_transitive : ∀ (R : A → A → Prop) x y z,
  refl_trans_clos R x y → refl_trans_clos R y z → refl_trans_clos R x z :=
  by
    intros R x y z tr_x_y
    induction' tr_x_y with _ _ _ _ _ _ ih
    . intros rest; trivial
    . intros rest
      apply refl_trans_clos.step; trivial
      apply ih; trivial


lemma refl_trans_is_trans_refl :
  refl_clos (trans_clos R) ≅ trans_clos (refl_clos R)
   :=
   by
    apply both_inclusions <;> intros x y hyp
    . cases hyp
      . constructor; constructor
      . apply trans_clos_monotone R
        -- this should be a lemma :/
        . intros; constructor; trivial
        . trivial
    . induction' hyp with _ _ rc _ _ _ rc step ih
      . cases rc
        . constructor
        . apply refl_clos.base
          apply trans_clos.base; trivial
      . cases rc; trivial
        apply refl_clos.base
        cases ih
        . apply trans_clos.base; trivial
        . apply trans_clos.step <;> trivial


lemma refl_sym_is_sym_refl :
  refl_clos (sym_clos R) ≅ sym_clos (refl_clos R)
  :=
  by
    apply both_inclusions <;> intros x y hyp
    . cases' hyp with _ base
      . constructor; constructor
      . cases base
        . constructor; apply refl_clos.base; trivial
        . apply sym_clos.inv
          apply refl_clos.base; trivial
    . cases' hyp with base base
      . cases base
        . constructor
        . apply refl_clos.base; constructor; trivial
      . cases base
        . constructor
        . apply refl_clos.base; apply sym_clos.inv; trivial


lemma refl_trans_sym_is_trans_sym_refl :
  refl_clos (trans_clos (sym_clos R)) ≅ trans_clos (sym_clos (refl_clos R)) :=
    by
      apply both_inclusions <;> intros
      . apply trans_clos_monotone
        . intros x y red
          apply (refl_sym_is_sym_refl _ _ _).1
          apply red
        . apply (refl_trans_is_trans_refl _ _ _).1
          trivial
      . apply (refl_trans_is_trans_refl _ _ _).2
        apply trans_clos_monotone
        . intros x y red
          apply  (refl_sym_is_sym_refl _ _ _).2
          apply red
        . trivial

lemma trans_is_refl_trans : ∀ x y : A, x ~>+ y → x ~>* y :=
by
  intros x y red
  induction red
  . apply refl_trans_clos.step; trivial
    constructor
  . case step red _ ih =>
    apply refl_trans_clos.step <;> trivial

lemma refl_trans_is_trans_or_eq : ∀ x y : A, x ~>* y → x = y ∨ x ~>+ y :=
by
  intros x y red
  induction red
  . left; trivial
  . case step red _ ih =>
    right; cases ih
    . apply trans_clos.base
      simp [*] at *; trivial
    . apply trans_clos.step <;> trivial

lemma refl_trans_step_is_trans : ∀ x y z : A, x ~> z → z ~>* y → x ~>+ y :=
by
  intros x y z red_x_z red_z_y
  revert red_x_z x
  induction red_z_y <;> intros x red_x_?
  . constructor; trivial
  . case step _ _ _ ih =>
    apply trans_clos.step; trivial
    apply ih; trivial


lemma sym_inv : ∀ (R : A → A → Prop), R⁻¹ ⊆ sym_clos R :=
 by intros R x y red
    apply sym_clos.inv; trivial

def diverge_from (x : A) : Prop :=
  ∃ xs : Nat → A, xs 0 = x ∧ ∀ n, xs n ~> xs (n+1)

def normalizes (x : A) : Prop := ¬ (diverge_from R x)

def normalizing : Prop := ∀ x : A, normalizes R x

def normal (x : A) : Prop := ¬ (∃ x', x ~> x')

theorem normal_normalizing (x : A) : normal R x → normalizes R x :=
by
  simp [normal]
  intros norm_x div_x
  match div_x with
    | Exists.intro xs (And.intro zero_case incr_case) =>
    apply norm_x (xs 1)
    rw [←zero_case]
    apply incr_case

-- An alternate way to define normality.
lemma normal_red : ∀ x y, normal R x → x ~>* y → x = y :=
by
  intros x y norm red
  cases red; trivial
  case step y _ _ =>
  by_contra
  apply norm; exists y

#check forall_and

-- I'm convinced this is somewhere in the standard library
theorem exists_iff : ∀ T (P Q : T → Prop),
        (∀ t, Q t ↔ P t) →
        (∃ t, P t) →
        ∃ t, Q t :=
by
  intros T P Q equiv ex_t
  match ex_t with
   | Exists.intro w h =>
     exists w
     simp [equiv]
     exact h


#print Classical.axiomOfChoice

theorem iterate_left : ∀ {A} (f : A → A) (n : ℕ) (x : A), f^[n+1] x = f (f^[n] x) :=
by
  intros A f n
  induction' n with n ihn
  . simp [Nat.iterate]
  . simp [Nat.add, Nat.iterate]
    intros x
    apply ihn

-- This is gonna need a clever application of AC!
lemma dependent_choice' : ∀ {A} (Q : A → A → Prop) (a : A),
      (∀ a, ∃ b, Q a b) →
      ∃ f : ℕ → A, f 0 = a ∧ ∀ n, Q (f n) (f (n+1)) :=
by
  intros A Q a forall_exists_Q
  have choice_aut : ∃ f : A → A, ∀ x, Q x (f x) :=
  by
    apply Classical.axiomOfChoice
    exact forall_exists_Q
  match choice_aut with
   | Exists.intro f h =>
       exists (λ n ↦ f^[n] a)
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
  (Q : A → A → Prop),
  Inhabited A →
  (∀ a, ∃ b, Q a b) →
  ∃ f : ℕ → A, ∀ n, Q (f n) (f (n+1)) :=
by
  intros A Q inhab forall_exists_Q
  have a : A := by match inhab with | Inhabited.mk a => exact a
  have h := dependent_choice' _ a forall_exists_Q
  match h with
  | Exists.intro f h' =>
    exists f
    apply h'.2

#print Subtype
#print Exists

lemma dependent_choice'' : ∀ (P : A → Prop)
  (Q : A → A → Prop) (a : A),
  P a →
  (∀ a, P a → ∃ b, P b ∧ Q a b) →
  ∃ f : ℕ → A, f 0 = a ∧ ∀ n, P (f n) ∧ Q (f n) (f (n+1)) :=
by
  intros P Q a pa ex
  have h : ∃ (f : ℕ → {x : A // P x}), f 0 = ⟨a, pa⟩
           ∧ ∀ n, P (f n) ∧ Q (f n) (f (n+1)) :=
  by
    apply (@dependent_choice' {x : A // P x} (λ p q => P p ∧ Q p q) _)
    intros ap
    match ap with
    | Subtype.mk a' p =>
      simp
      apply And.intro
      . exact p
      . match (ex a' p) with
        | Exists.intro b ⟨pb, qb⟩ => exists (Subtype.mk b pb)
  match h with
  | Exists.intro f ⟨zf, sf⟩ =>
    exists (λ n ↦ (f n).val)
    simp; rw [zf]; simp
    intros n; apply sf

-- This is the "real" def of normalization, or at least the
-- one that's actually useful.
lemma normalizes_ind : ∀ P : A → Prop,
  (∀ x, (∀ y, x ~> y → P y) → P x) → ∀ x, normalizes R x → P x :=
by
  intros P IH x norm
  apply Classical.byContradiction
  intro h; apply norm
  have h' : ∃ f : ℕ → A, f 0 = x ∧ ∀ n, ¬ P (f n) ∧ f n ~> f (n+1) :=
  by
    apply (dependent_choice''  (λ a ↦ ¬ P a))
    . exact h
    . intros a npa
      apply Classical.byContradiction
      simp; intros p
      apply npa
      apply IH; intros y ry
      apply Classical.byContradiction; intros npy
      apply (p y npy ry)

  rw [diverge_from]
  match h' with
    | Exists.intro xs ⟨P0, P1⟩ =>
      exists xs
      apply And.intro
      . exact P0
      . intros n
        apply (P1 n).2



lemma normalizing_ind : ∀ P : A → Prop,
  (∀ x, (∀ y, x ~> y → P y) → P x) → normalizing R → ∀ x, P x :=
by
  intros P IH norm x
  apply normalizes_ind
  . apply IH
  . apply norm


lemma ind_normalizing :
   (∀ P : A → Prop, (∀ x, (∀ y, x ~> y → P y) → P x) → ∀ x, P x) → normalizing R :=
by
  intros ih
  intros x
  apply ih
  intros x red_norm
  intro div
  cases div
  case a.intro f h =>
    apply red_norm
    . simp [← h.1]
      apply h.2 0
    . exists (λ n ↦ f (n+1))
      simp
      intros n; apply h.2

-- Should be easy!
lemma red_ref_trans_clos : ∀ x y z, x ~> y → refl_trans_clos R y z → refl_trans_clos R x z :=
by
  intros x y z red_x_y h
  apply refl_trans_clos.step _ _ <;> trivial


#check Classical.em

lemma normalizing_normal (x : A) : normalizes R x → ∃ y : A, x ~>* y ∧ normal R y
:=
by
  apply normalizes_ind
  intros x h
  by_cases (∃ y, x ~> y)
  . cases' h with y h'
    cases' h _ h' with z h''
    cases h''
    exists z
    constructor
    . apply refl_trans_clos.step
      . apply h'
      . trivial
    . trivial
  . exists x
    constructor
    . apply refl_trans_clos.refl
    . apply h

def joins : ∀ (_x _y : A), Prop := λ x y ↦ ∃ z : A, x ~>* z ∧ y ~>* z

def wedge : A → A → Prop := λ (u v : A) ↦ ∃ t, t ~>* u ∧ t ~>* v

infix:50 " ~>*.*<~ " => joins R
infix:50 " *<~.~>* " => wedge R

def church_rosser := ∀ (x y : A), x <~>* y → x ~>*.*<~ y

def confluent := ∀ (y z : A), y *<~.~>* z → y ~>*.*<~ z

def diamond :=
  ∀ x y z : A, x ~> y → x ~> z → ∃ w, y ~> w ∧ z ~> w

def weakly_confluent :=
  ∀ x y z : A, x ~> y → x ~> z → y ~>*.*<~ z

def semi_confluent :=
  ∀ x y z : A, x ~> y → x ~>* z → y ~>*.*<~ z

-- let's relate all of these

lemma refl_trans_sym_refl_trans :
  ∀ R, refl_trans_clos R ⊆ refl_trans_sym_clos R :=
by
  intros R x y red
  induction red; constructor
  apply refl_trans_sym_clos.trans <;> try trivial
  apply refl_trans_sym_clos.base; trivial


lemma wedge_inc_refl_sym_trans : wedge R ⊆ (. <~>* .) :=
  by
    intros x y wedge
    cases' wedge with w h
    cases' h with h1 h2
    apply (refl_trans_sym_clos.trans _ w)
    . apply refl_trans_sym_clos.inv
      apply refl_trans_sym_refl_trans; trivial
    . apply refl_trans_sym_refl_trans; trivial

-- this one is trivial
lemma church_rosser_implies_confluent : church_rosser R → confluent R :=
  by
    intros cr y z wedge
    have h : y <~>* z := by
      apply wedge_inc_refl_sym_trans
      exact wedge
    apply cr
    trivial

-- quite useful manipulations
lemma swap_joins : ∀ x y, x ~>*.*<~ y → y ~>*.*<~ x :=
by
  intros x y joins
  cases' joins with z h
  cases h
  exists z

lemma red_joins : ∀ x y z, x ~> y → y ~>*.*<~ z → x ~>*.*<~ z :=
by
  intros x y z red_x_y joins_y_z
  cases' joins_y_z with w h
  cases h
  exists w; constructor
  . apply refl_trans_clos.step <;> trivial
  . trivial

lemma reds_joins_left : ∀ x y z, x ~>* y → y ~>*.*<~ z → x ~>*.*<~ z :=
by
  intros x y z red_x_y joins_y_z
  induction' red_x_y with _ _ _ _ _ _ ih
  . trivial
  . apply red_joins
    . trivial
    . have h' := ih joins_y_z
      trivial

lemma reds_joins_right : ∀ x y z, x ~>* z → y ~>*.*<~ z → y ~>*.*<~ x :=
by
  intros x y z red_x_y joins_y_z
  apply swap_joins
  have joins_z_y := swap_joins _ _ _ joins_y_z
  apply (reds_joins_left _ x z y) <;> trivial

-- this one is surprising, but not too tough.
lemma semi_confluent_implies_confluent : semi_confluent R → confluent R :=
by
  intros semi x y wedge
  cases' wedge with w h
  cases' h with h1 h2
  revert h2 y
  induction' h1 with z x y y' red_x_y _red_y_y' ih <;> intros z red_x_z
  . exists z; constructor
    . trivial
    . constructor
  . have h := semi x y z red_x_y red_x_z
    cases' h with z' h
    cases' h with h1 h2
    have ih := ih z' h1
    apply reds_joins_right <;> trivial


-- This has a very simple "diagram proof":
--
--                       x
--                     /   \
--                    / \ / \
--                   y  ...  z
--                    \ / \ /
--                      \ /
--                       ?
-- The formal proof is more subtle and uses the previous lemma.
theorem diamond_implies_confluent : diamond R → confluent R :=
by
  intros sc
  apply semi_confluent_implies_confluent
  unfold semi_confluent
  intros x y z red h
  revert y
  induction h
  -- FIXME trivial case (eauto)
  case a.refl _ =>
    intros y _; exists y; constructor
    . constructor
    . constructor; trivial; constructor
  case a.step a b c red_a_b _red_b_c ih =>
    intros d red_a_d
    have h := (sc _ _ _ red_a_b red_a_d)
    cases' h with e h
    cases' h with red_b_e red_d_e
    apply red_joins; apply red_d_e
    apply ih; trivial

-- also trivial
lemma confluent_implies_weakly_confluent : confluent R → weakly_confluent R :=
by
  intros confl x y z red_x_y red_x_z
  apply confl; exists x; constructor <;> apply refl_trans_clos.step <;> try constructor
  . trivial
  . trivial

-- this one is a little more work.
-- again, something clear from a diagram requires a tedious mechanical proof
lemma confluent_implies_church_rosser : confluent R → church_rosser R :=
by
  intros confl
  unfold church_rosser
  intros x y red_x_y
  induction red_x_y
  case refl x =>
    exists x ; repeat constructor
  case base x y red_x_y =>
    exists y; constructor
    . apply refl_trans_clos.step; trivial; constructor
    . constructor
  case trans x y z red_x_y red_y_z joins_x_y joins_y_z =>
    cases' joins_x_y with w1 h1
    cases' h1 with h11 h12
    cases' joins_y_z with w2 h2
    cases' h2 with h21 h22
    have h' : wedge R w1 w2 := by
      exists y
    have h := confl w1 w2 h'
    cases' h with w h''
    exists w; cases' h'' with h3 h4
    constructor <;> apply refl_trans_clos_transitive <;> trivial
  case inv _ h =>
    cases' h with w h'
    cases' h' with h1 h2
    exists w

-- Weakly confluent does not imply confluent in general!
inductive X := | a | b | c | d

-- a <- b <=> c -> d

-- This definition is a bit tedious because of dependent matching.
/- inductive RX : X → X → Prop :=
  | r_b_a : RX b a
  | r_b_c : RX b c
  | r_c_b : RX c b
  | r_c_d : RX c d
 -/
-- This one works great with simp and friends
def RX : X → X → Prop :=
  open X in
  λ x y ↦
    (x = b ∧ y = a)
  ∨ (x = b ∧ y = c)
  ∨ (x = c ∧ y = b)
  ∨ (x = c ∧ y = d)

lemma not_joins_a_d : ¬ joins RX X.a X.d :=
by
  intros h
  cases' h with w h
  cases' h with h1 h2
  have eq_a : X.a = w := by
    apply normal_red RX
    . intros h
      cases' h with w h
      simp [RX] at h
    . apply h1
  have eq_d : X.d = w := by
    apply normal_red RX
    . intros h
      cases' h with w h
      simp [RX] at h
    . apply h2
  simp [← eq_a] at eq_d


lemma weakly_confluent_does_not_imply_confluent : ∃ (A : Type) (R : A → A → Prop),
weakly_confluent R ∧ ¬ confluent R :=
by
  exists X, RX
  constructor
  . intros x y z r_x_y r_x_z
    simp [RX] at r_x_y
    simp [RX] at r_x_z
    -- ugh this is tedious. Probably there's some nuclear tactic here
    cases r_x_y <;> cases r_x_z <;> simp [*] at *
    . exists X.a; repeat constructor
    . exists X.a; try constructor
      . constructor
      . simp [*]; constructor; simp [RX]
        . left; trivial
        . constructor; simp [RX]; left; trivial; constructor
    . exists X.a; simp [*]; constructor
      . repeat (constructor; simp [RX]; left; trivial)
        constructor
      . constructor
    . case inr h1 h2 =>
      cases h1 <;> cases h2 <;> simp [*] at *
      . exists X.c; repeat constructor
      . case inr h1 h2 =>
        cases h1 <;> cases h2 <;> simp [*] at *
        . exists X.b; repeat constructor
        . exists X.d; constructor
          . constructor; simp [RX]; right; trivial
            constructor; simp [RX]; right; trivial
            constructor
          . constructor
        . exists X.d; constructor
          . constructor
          . constructor; simp [RX]; right; trivial
            constructor; simp [RX]; right; trivial
            constructor
        . exists X.d; repeat constructor
  . intros h
    apply not_joins_a_d
    apply h
    exists X.b; constructor
    . constructor
      simp [RX]
      left; trivial
      constructor
    . constructor
      simp [RX]
      right; trivial
      constructor
      . simp [RX]; right; trivial
      . constructor


inductive close_below (P : A → Prop) : A → Prop :=
  | here : ∀ x, P x → close_below P x

-- Sometimes it's easier to work with the transitive closure for WF induction.
lemma normalizes_trans : normalizing R → normalizing (. ~>+ .) :=
by
  intros norm
  apply ind_normalizing
  intros P ih
  let Q := λ x ↦ P x ∧ ∀ y, x ~>+ y → P y
  have h : ∀ x, Q x :=
  by
    intros x
    apply normalizing_ind R
    . intros x ih'
      constructor
      . apply ih
        intros y red_x_y
        cases red_x_y
        . apply (ih' _ _).1
          trivial
        . apply (ih' _ _).2 <;> trivial
      -- FIXME: complete duplication!
      . intros y red_x_y
        cases red_x_y
        . apply (ih' _ _).1
          trivial
        . apply (ih' _ _).2 <;> trivial
    . trivial
  intros x; apply (h x).1

-- When proving confluence, it's actually tedious to always handle the reflexive case.
def confluent' := ∀ x y z : A, x ~>+ y → x ~>+ z → y ~>*.*<~ z

lemma confluent'_implies_confluent : confluent' R → confluent R :=
by
  intros conf'
  apply semi_confluent_implies_confluent
  intros x y z red_x_y red_x_z
  have h := refl_trans_is_trans_or_eq _ _ _ red_x_z
  cases h
  . case a.inl h =>
    simp [← h]
    exists y; repeat constructor
    trivial
    constructor
  . apply conf'
    . constructor; trivial
    . trivial


-- but if R is normalizing...
theorem newmans_lemma : normalizing R → weakly_confluent R → confluent R :=
  -- Requires a clever induction on diagrams
by
  intros norm_R weak
  intros y z wedge
  cases wedge
  case intro x h =>
  revert h z y
  have norm_trans := normalizes_trans _ norm_R
  have h :=
    normalizes_ind (. ~>+ .)
    (λ x ↦ ∀ y z, x ~>* y ∧ x ~>* z → y ~>*.*<~ z)
  intros y z wedge
  (apply h <;> try trivial) <;> try apply norm_trans
  clear h
  intros x ih y z wedge
  -- FIXME: this is horrid
  cases wedge.1
  . exists z; constructor; apply wedge.2; constructor
  . case a.step y' red_x_y' red_y'_y =>
    cases wedge.2
    . exists y; constructor; constructor
      apply wedge.1
    . case step z' red_x_z' red_z'_z =>
      -- finally use weak confluence
      have join1 := weak _ _ _ red_x_y' red_x_z'
      cases' join1 with w h'
      have join2 :=
        ih y' (trans_clos.base _ _ red_x_y') y w
          (And.intro red_y'_y h'.1)
      have join3 := ih z' (trans_clos.base _ _ red_x_z') w z
          (And.intro h'.2 red_z'_z)
      cases' join2 with w1 h1
      cases' join3 with w2 h2
      have red_x_w : x ~>+ w :=
        by
          apply refl_trans_step_is_trans
          . apply red_x_z'
          . apply h'.2
      have join4 := ih w red_x_w w1 w2
        (And.intro h1.2 h2.1)
      cases' join4 with omega h3
      exists omega; constructor
      . apply refl_trans_clos_transitive
        . apply h1.1
        . apply h3.1
      . apply refl_trans_clos_transitive
        . apply h2.2
        . apply h3.2

lemma confluent_unique_nf : confluent R →
  ∀ x y z, x ~>* y → x ~>*z → normal R y → normal R z → y = z :=
by
  intros conf x y z red_x_y red_x_z norm_y norm_z
  have wdg_y_z : wedge _ y z := Exists.intro x ⟨ red_x_y, red_x_z ⟩
  have h : y ~>*.*<~ z := conf _ _ wdg_y_z
  cases' h with w h
  cases h
  have eq_y_w : y = w := by apply normal_red <;> trivial
  have eq_z_w : z = w := by  apply normal_red <;> trivial
  simp [*]

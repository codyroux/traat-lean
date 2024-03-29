import Mathlib.Logic.Function.Iterate
import Aesop

section variable {A : Type}

section variable (R : A → A → Prop)

section variable [inhabited_A : Nonempty A]

-- These are a little ad-hoc but they'll serve

@[aesop unsafe [constructors, cases]]
inductive trans_clos (R : A → A → Prop) : A → A → Prop
| base : ∀ a b, R a b → trans_clos R a b
| step : ∀ a b c, R a b → trans_clos R b c → trans_clos R a c

@[aesop unsafe [constructors, cases]]
inductive refl_clos (R  : A → A → Prop) : A → A → Prop where
| refl : ∀ a, refl_clos R a a
| base : ∀ a b, R a b → refl_clos R a b

@[aesop unsafe [constructors, cases]]
inductive sym_clos (R  : A → A → Prop) : A → A → Prop
| base : ∀ a b, R a b → sym_clos R a b
| inv : ∀ a b, R b a → sym_clos R a b

@[aesop unsafe [constructors, cases]]
inductive refl_trans_clos (R  : A → A → Prop) : A → A → Prop :=
| refl : ∀ a, refl_trans_clos R a a
| step : ∀ a b c, R a b → refl_trans_clos R b c → refl_trans_clos R a c

@[aesop unsafe [constructors, cases]]
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
postfix:100 " ⁻¹ " => (λ (R : A → A → Prop) x y ↦ R y x)
infixl:50 " ~> " => R
infixl:50 " ~>= "   => refl_clos R
infixl:50 " ~>+ "   => trans_clos R
infixl:50 " ~>* "   => refl_trans_clos R
infixl:50 " <~>* "  => refl_trans_sym_clos R

lemma both_inclusions : R ⊆ R' → R' ⊆ R → R ≅ R' := by aesop

lemma equiv_left : R ≅ R' → R ⊆ R' := by aesop

lemma equiv_right : R ≅ R' → R' ⊆ R := by aesop


@[simp]
lemma trans_clos_monotone : R ⊆ R' →  trans_clos R ⊆ trans_clos R' :=
  by
    intros le x y tr
    induction tr <;> aesop

@[simp]
lemma sym_clos_monotone : R ⊆ R' →  sym_clos R ⊆ sym_clos R' :=
   by
    intros le x y sym
    induction sym <;> aesop

@[simp]
lemma refl_clos_monotone : R ⊆ R' →  refl_clos R ⊆ refl_clos R' :=
  by
    intros le x y refl
    induction refl <;> aesop


lemma trans_clos_transitive : trans_clos R x y → trans_clos R y z → trans_clos R x z :=
  by
    intros tr_x_y
    induction tr_x_y <;> aesop

@[aesop unsafe 5%]
lemma refl_trans_clos_transitive : refl_trans_clos R x y → refl_trans_clos R y z → refl_trans_clos R x z :=
  by
    intros tr_x_y
    induction tr_x_y <;> aesop


lemma refl_trans_is_trans_refl :
  refl_clos (trans_clos R) ≅ trans_clos (refl_clos R)
   :=
   by
    apply both_inclusions <;> intros x y hyp
    . cases hyp
      . aesop
      . apply trans_clos_monotone R <;> aesop
    . induction' hyp with _ _ rc _ _ _ rc step ih
      . cases rc <;> aesop
      . cases rc; trivial
        apply refl_clos.base; aesop

@[simp]
lemma refl_sym_is_sym_refl :
  refl_clos (sym_clos R) ≅ sym_clos (refl_clos R)
  :=
  by
    apply both_inclusions <;> intros x y hyp <;> aesop

@[simp]
lemma refl_trans_clos_monotone : R ⊆ R' →  refl_trans_clos R ⊆ refl_trans_clos R' :=
  by
    intros le x y refl
    induction refl <;> aesop

lemma refl_trans_sym_is_trans_sym_refl :
  refl_clos (trans_clos (sym_clos R)) ≅ trans_clos (sym_clos (refl_clos R)) :=
    by
      apply both_inclusions <;> intros
      . apply trans_clos_monotone
        . intros
          apply (refl_sym_is_sym_refl _ _ _).1
          trivial
        . apply (refl_trans_is_trans_refl _ _ _).1
          trivial
      . apply (refl_trans_is_trans_refl _ _ _).2
        apply trans_clos_monotone
        . intros x y red
          apply  (refl_sym_is_sym_refl _ _ _).2
          trivial
        . trivial

lemma trans_is_refl_trans : x ~>+ y → x ~>* y :=
by
  intros red
  induction red <;> aesop

lemma refl_trans_is_trans_or_eq : x ~>* y → x = y ∨ x ~>+ y :=
by
  intros red
  induction red <;> aesop

lemma refl_trans_step_is_trans : x ~> z → z ~>* y → x ~>+ y :=
by
  intros red_x_z red_z_y
  revert red_x_z x
  induction red_z_y <;> aesop

@[simp]
lemma sym_inv : R⁻¹ ⊆ sym_clos R := by aesop

def diverge_from (x : A) : Prop :=
  ∃ xs : Nat → A, xs 0 = x ∧ ∀ n, xs n ~> xs (n+1)

def normalizes (x : A) : Prop := ¬ (diverge_from R x)

def normalizing : Prop := ∀ x : A, normalizes R x

def normal (x : A) : Prop := ¬ (∃ x', x ~> x')

theorem normal_normalizing : normal R x → normalizes R x :=
by
  simp [normal]
  intros norm_x div_x
  match div_x with
    | Exists.intro xs (And.intro zero_case incr_case) =>
    apply norm_x (xs 1)
    rw [←zero_case]
    apply incr_case

-- An alternate way to define normality.
lemma normal_red : normal R x → x ~>* y → x = y :=
by
  intros norm red
  cases red; trivial
  case step y _ _ =>
  by_contra
  apply norm; exists y


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
      exists xs; aesop

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
  intros ih x
  apply ih
  intros x red_norm div
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

lemma normalizing_normal : normalizes R x → ∃ y : A, x ~>* y ∧ normal R y
:=
by
  apply normalizes_ind
  intros x h
  by_cases (∃ y, x ~> y)
  . cases' h with y h'
    cases' h _ h' with z h''
    cases h''
    exists z
    constructor <;> aesop
  . exists x; constructor
    . constructor
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
  aesop

@[simp]
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
    aesop

-- quite useful manipulations
lemma swap_joins : x ~>*.*<~ y → y ~>*.*<~ x :=
by
  intros joins
  cases' joins with z h
  cases h
  exists z

lemma red_joins : x ~> y → y ~>*.*<~ z → x ~>*.*<~ z :=
by
  intros red_x_y joins_y_z
  cases' joins_y_z with w h
  cases h
  exists w; aesop

@[simp]
lemma reds_joins_left : x ~>* y → y ~>*.*<~ z → x ~>*.*<~ z :=
by
  intros red_x_y joins_y_z
  induction' red_x_y with _ _ _ _ _ _ ih
  . trivial
  . apply red_joins
    . trivial
    . have h' := ih joins_y_z
      trivial

@[simp]
lemma reds_joins_right : x ~>* z → y ~>*.*<~ z → y ~>*.*<~ x :=
by
  intros red_x_y joins_y_z
  apply swap_joins
  have joins_z_y := swap_joins _ joins_y_z
  apply (reds_joins_left _) <;> trivial

-- this one is surprising, but not too tough.
lemma semi_confluent_implies_confluent : semi_confluent R → confluent R :=
by
  intros semi x y wedge
  cases' wedge with w h
  cases' h with h1 h2
  revert h2 y
  induction' h1 with z x y y' red_x_y _red_y_y' ih <;> intros z red_x_z
  . exists z; aesop
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
    intros y _
    exists y; aesop
  case a.step a b c red_a_b _red_b_c ih =>
    intros d red_a_d
    have h := (sc _ _ _ red_a_b red_a_d)
    cases' h with e h
    cases' h with red_b_e red_d_e
    apply red_joins <;> aesop

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
    exists y; constructor <;> aesop
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
@[aesop safe [constructors, cases]]
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
@[simp]
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
    apply normal_red RX <;> aesop
  have eq_d : X.d = w := by
    apply normal_red RX <;> aesop
  simp [← eq_a] at eq_d


lemma weakly_confluent_does_not_imply_confluent : ∃ (A : Type) (R : A → A → Prop),
weakly_confluent R ∧ ¬ confluent R :=
by
  exists X, RX
  constructor
  . intros x y z r_x_y r_x_z
    simp [*] at r_x_y
    simp [*] at r_x_z
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
        . apply (ih' _ _).1; trivial
        . apply (ih' _ _).2 <;> trivial
      -- FIXME: complete duplication!
      . intros y red_x_y
        cases red_x_y
        . apply (ih' _ _).1; trivial
        . apply (ih' _ _).2 <;> trivial
    . trivial
  intros x; apply (h x).1

-- When proving confluence, it's sometimes tedious to always handle the reflexive case.
def confluent' := ∀ x y z : A, x ~>+ y → x ~>+ z → y ~>*.*<~ z

lemma confluent'_implies_confluent : confluent' R → confluent R :=
by
  intros conf'
  apply semi_confluent_implies_confluent
  intros x y z red_x_y red_x_z
  have h := refl_trans_is_trans_or_eq _ red_x_z
  cases h
  . case a.inl h =>
    simp [← h]
    exists y; aesop
  . apply conf' <;> aesop

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
  . exists z; aesop
  . case a.step y' red_x_y' red_y'_y =>
    cases wedge.2
    . exists y; aesop
    . case step z' red_x_z' red_z'_z =>
      -- finally use weak confluence
      have join1 := weak _ _ _ red_x_y' red_x_z'
      cases' join1 with w h'
      have join2 : y ~>*.*<~ w :=
      by
        apply ih
        . apply trans_clos.base
          apply red_x_y'
        . aesop
      have join3 : z ~>*.*<~ w :=
      by
        apply ih
        . apply trans_clos.base
          apply red_x_z'
        . aesop
      cases' join2 with w1 h1
      cases' join3 with w2 h2
      have red_x_w : x ~>+ w :=
        by
          apply refl_trans_step_is_trans
          . apply red_x_z'
          . apply h'.2
      have join4 : w1 ~>*.*<~ w2 :=
      by
        apply ih
        . apply red_x_w
        . aesop
       /- ih w red_x_w w1 w2
        (And.intro h1.2 h2.1) -/
      cases' join4 with omega h3
      exists omega; constructor
      . apply refl_trans_clos_transitive
        . apply h1.1
        . apply h3.1
      . apply refl_trans_clos_transitive
        . apply h2.1
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

variable (S : A → A → Prop)

infix:50 " ++> " => S
infix:60 " ++>* " => refl_trans_clos S

lemma inc_refl_trans_eq : (. ~> .) ⊆ (. ++> .) → (. ++> .) ⊆ (. ~>* .) → (. ++>* .) ≅ (. ~>* .) :=
by
  simp
  intros r_sub_s s_sub_r_star x y; constructor <;> intros steps
  . induction steps
    . constructor
    . apply refl_trans_clos_transitive
      . apply s_sub_r_star; trivial
      . trivial
  . induction steps
    . constructor
    . aesop

lemma equiv_conf : S ≅ R → confluent S → confluent R :=
by
  simp
  intros equiv
  simp [confluent, wedge, joins]
  intros h y z x red_x_y red_y_z
  have h1 : refl_trans_clos S x y := by
    apply refl_trans_clos_monotone
    intros _ _; apply (equiv _ _).2
    trivial
  have h2 : refl_trans_clos S x z := by
    apply refl_trans_clos_monotone
    intros _ _; apply (equiv _ _).2
    trivial
  cases' (h y z x h1 h2) with w h
  cases' h with h1 h2
  exists w
  constructor <;> apply refl_trans_clos_monotone
  . intros x y; apply (equiv _ _).1
  . trivial
  . intros x y; apply (equiv _ _).1
  . trivial


lemma trans_clos_idempotent : ∀ R, refl_trans_clos (refl_trans_clos R) ≅ refl_trans_clos R :=
by
  simp; intros R x y
  constructor <;> intros steps <;> induction' steps with z a b c red_a_c _red_b_c ih
  . constructor
  . apply refl_trans_clos_transitive <;> trivial
  . constructor
  . apply refl_trans_clos.step
    . apply refl_trans_clos.step; trivial
      constructor
    . trivial

@[simp]
lemma conf_trans_clos : confluent (refl_trans_clos R) ↔ confluent R :=
by
  simp [confluent, joins, wedge]; constructor
  . intros h y z x red_x_y red_x_z
    have h1 : refl_trans_clos (refl_trans_clos R) x y :=
      by
        apply (trans_clos_idempotent _ _ _).2; trivial
    have h2 : refl_trans_clos (refl_trans_clos R) x z :=
      by
        apply (trans_clos_idempotent _ _ _).2; trivial
    cases' (h _ _ _ h1 h2) with w h
    cases' h with h1 h2
    exists w; constructor <;> apply (trans_clos_idempotent _ _ _).1 <;> trivial
  . intros h y z x red_x_y red_x_z
    have h1 : refl_trans_clos R x y :=
      by
        apply (trans_clos_idempotent _ _ _).1; trivial
    have h2 : refl_trans_clos R x z :=
      by
        apply (trans_clos_idempotent _ _ _).1; trivial
    cases' (h _ _ _ h1 h2) with w h
    cases' h with h1 h2
    exists w; constructor <;> apply (trans_clos_idempotent _ _ _).2 <;> trivial

lemma inc_refl_trans_confl : (. ~> .) ⊆ (. ++> .) → (. ++> .) ⊆ (. ~>* .) → confluent S → confluent R :=
by
  simp
  intros
  apply (conf_trans_clos _).1
  apply equiv_conf
  . apply inc_refl_trans_eq; simp
    . trivial
    . simp; trivial
  . aesop

lemma refl_is_refl_trans : x ~>= y → x ~>* y := by aesop

def strongly_confluent := ∀ x y z, x ~> y → x ~> z → ∃ w, y ~>* w ∧ z ~>= w

lemma strong_confluent_implies_confluent : strongly_confluent R → confluent R :=
by
  intros str_conf
  apply semi_confluent_implies_confluent
  unfold semi_confluent
  intros x y z red_x_y red_x_z
  revert red_x_y y
  induction' red_x_z with a x x₂ xₙ red_x_x2 red_x2_xn ih
  . intros y _; exists y; aesop
  . intros y red_x_y
    cases' (str_conf _ _ _ red_x_y red_x_x2) with y₂ h
    cases h.2
    . exists xₙ; constructor
      . apply refl_trans_clos_transitive
        . apply h.1
        . trivial
      . constructor
    . have ih : y₂ ~>*.*<~ xₙ :=
        by apply ih; trivial
      cases' ih with w _
      exists w; constructor
      . apply refl_trans_clos_transitive
        . apply h.1
        . aesop
      . aesop

infix:50 " ~>₁ " => R
infix:50 " ~>₂ " => S
infix:50 " ~>₁* " => refl_trans_clos R
infix:50 " ~>₂* " => refl_trans_clos S
infix:200 " ∪ " => λ R S x y ↦ R x y ∨ S x y

-- This would look a little nicer with some notation.
-- but the idea is that you can "re-order" steps so that
-- the 1 (resp 2) steps come first.
-- Note that this is a very strong condition!
-- It basically means that ~>₁ steps can "ignore" ~>₂
-- steps entirely and vice versa.
def commute := ∀ x y z, x ~>₁* y → x ~>₂* z →
               ∃ w, y ~>₂* w ∧ z ~>₁* w

infix:200 " ∘ " => λ R S x y ↦ ∃ z, R x z ∧ S z y

lemma refl_trans_union_left : (. ~>₁* .) ⊆ refl_trans_clos (R∪S) :=
by
  simp; intros x y red_x_y
  induction red_x_y <;> aesop

lemma refl_trans_union_right : (. ~>₂* .) ⊆ refl_trans_clos (R∪S) :=
by
  simp; intros x y red_x_y
  induction red_x_y <;> aesop

-- Ok this means we can break down confluence into pieces.
lemma commuting_confluence_implies_confluence :
  commute R S → confluent R → confluent S → confluent (R ∪ S)
:=
  by --let's apply some of our machinery
    intros commut_r_s conf_r conf_s
    apply inc_refl_trans_confl
    . have h : R ∪ S ⊆ (. ~>₁* .) ∘ (. ~>₂* .) :=
        by
          simp; intros x y red_or
          cases red_or
          . exists y; aesop
          . exists x; aesop
      apply h
    . simp
      intros x y z red_x_z red_z_y
      apply refl_trans_clos_transitive
      . apply refl_trans_union_left
        trivial
      . apply refl_trans_union_right; trivial
    . apply diamond_implies_confluent
      simp [diamond]
      intros x y z y1 red_x_y1 red_y1_y
      intros z1 red_x_z1 red_z1_z
      have wedge_y1_z1 : wedge R y1 z1 :=
        by exists x
      have join_y1_z1 := conf_r _ _ wedge_y1_z1
      cases' join_y1_z1 with w h
      clear wedge_y1_z1
      have h1 := commut_r_s _ _ _ h.1 red_y1_y
      have h2 := commut_r_s _ _ _ h.2 red_z1_z
      cases' h1 with w1 h1
      cases' h2 with w2 h2
      have wedge_w1_w2 : wedge S w1 w2 :=
        by exists w; aesop
      have join_w1_w2 : joins S w1 w2 := by apply conf_s; trivial
      cases' join_w1_w2 with omega h3
      clear wedge_w1_w2
      exists omega; constructor
      . exists w1; aesop
      . exists w2; aesop

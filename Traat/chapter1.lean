import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Basic

@[grind]
class Red (A : Type) where
  reduces : A → A → Prop

open Red

instance invRed {A : Type} : Inv (A → A → Prop) where
  inv R x y := R y x

infixl:50 " ~> " => reduces

@[grind]
inductive trans_clos {A : Type} (R : A → A → Prop) : A → A → Prop
| base : ∀ a b, R a b → trans_clos R a b
| step : ∀ a b c, R a b → trans_clos R b c → trans_clos R a c

@[grind]
inductive refl_clos {A : Type} (R : A → A → Prop) : A → A → Prop where
| refl : ∀ a, refl_clos R a a
| base : ∀ a b, R a b → refl_clos R a b

@[grind]
inductive sym_clos {A : Type} (R : A → A → Prop) : A → A → Prop
| base : ∀ a b, R a b → sym_clos R a b
| inv : ∀ a b, R b a → sym_clos R a b

@[grind]
inductive refl_trans_clos {A : Type} (R : A → A → Prop) : A → A → Prop where
| refl : ∀ a, refl_trans_clos R a a
| step : ∀ a b c, R a b → refl_trans_clos R b c → refl_trans_clos R a c

@[grind]
inductive refl_trans_sym_clos {A : Type} (R : A → A → Prop) : A → A → Prop where
| refl : ∀ a, refl_trans_sym_clos R a a
| base : ∀ a b, R a b → refl_trans_sym_clos R a b
| trans : ∀ a b c, refl_trans_sym_clos R a b →
                   refl_trans_sym_clos R b c →
                   refl_trans_sym_clos R a c
| inv : ∀ a b, refl_trans_sym_clos R b a →
               refl_trans_sym_clos R a b

@[simp]
def refl_clos_red [R : Red A] := refl_clos R.reduces
@[simp]
def sym_clos_red [R : Red A] := sym_clos R.reduces
@[simp]
def trans_clos_red [R : Red A] := trans_clos R.reduces
@[simp]
def refl_trans_clos_red [R : Red A] := refl_trans_clos R.reduces
@[simp]
def refl_trans_sym_clos_red [R : Red A] := refl_trans_sym_clos R.reduces

infixl:50 " ~>= "   => refl_clos_red
infixl:50 " <~> "   => sym_clos_red
infixl:50 " ~>+ "   => trans_clos_red
infixl:50 " ~>* "   => refl_trans_clos_red
infixl:50 " <~>* "  => refl_trans_sym_clos_red

@[simp]
lemma incRed {A : Type} (R R' : A → A → Prop) (x y : A) : R ≤ R' → R x y → R' x y := by
  simp [LE.le]; grind

@[simp, grind .]
lemma incRelRelated {A} {R : Red A} {R' : Red A} x y : R.reduces ≤ R'.reduces → reduces (self:=R) x y → reduces (self:=R') x y := by
  simp [LE.le]; grind

@[simp, grind .]
lemma both_inclusions {A : Type} {R R' : A → A → Prop} : R ≤ R' → R' ≤ R → R = R' := by
  grind

@[simp, grind .]
lemma equiv_left {A : Type} {R R' : A → A → Prop} : R = R' → R ≤ R' := by
  grind

@[simp, grind .]
lemma equiv_right {A : Type} {R R' : A → A → Prop} : R = R' → R' ≤ R := by
  grind only

@[simp]
lemma trans_clos_monotone {A : Type} (R R' : A → A → Prop) : R ≤ R' →
  trans_clos R ≤ trans_clos R' := by
  intros le x y tr
  induction tr <;> simp [LE.le] at * <;> grind


@[simp]
lemma refl_trans_clos_monotone {A : Type} (R R' : A → A → Prop) : R ≤ R' →
  refl_trans_clos R ≤ refl_trans_clos R' := by
  intros le x y tr
  induction tr <;> simp [LE.le] at * <;> grind


@[simp]
lemma sym_clos_monotone {A : Type} (R R' : A → A → Prop) : R ≤ R' → sym_clos R ≤ sym_clos R' := by
  intros le x y sym
  induction sym <;> simp [LE.le] at * <;> grind


lemma refl_clos_monotone {A : Type} (R R' : A → A → Prop)
 : R ≤ R' → refl_clos R ≤ refl_clos R' :=
  by
    intros le x y re
    induction re <;> simp [LE.le] at * <;> grind

lemma sym_clos_sym [R : Red A] (x y : A)
  (h : x <~> y)
  : y <~> x := by
  simp at *
  induction h <;> grind

lemma trans_clos_transitive [R : Red A] (x y z : A)
  (h₁ : x ~>+ y)
  (h₂ : y ~>+ z)
  : x ~>+ z := by
  revert h₂ z
  simp at *
  induction h₁ <;> grind

@[grind <=]
lemma trans_clos_transitive' (R : A → A → Prop) (x y z : A)
  (h₁ : trans_clos R x y)
  (h₂ : trans_clos R y z)
  : trans_clos R x z := by
  revert h₂ z
  induction h₁ <;> grind

@[grind →]
lemma refl_trans_clos_transitive [R : Red A] (x y z : A)
  (h₁ : x ~>* y) (h₂ : y ~>* z) : x ~>* z := by
  revert h₂ z
  simp at *
  induction h₁ <;> grind

@[grind <=]
lemma refl_trans_clos_transitive' (R : A → A → Prop) (x y z : A)
  (h₁ : refl_trans_clos R x y)
  (h₂ : refl_trans_clos R y z)
  : refl_trans_clos R x z := by
  revert h₂ z
  induction h₁ <;> grind


lemma refl_trans_is_trans_refl (R : A → A → Prop) :
  refl_clos (trans_clos R) = trans_clos (refl_clos R) := by
  funext x y
  apply propext
  constructor <;> intros h
  . induction h
    case mp.refl => grind
    case mp.base z h =>
      induction h <;> grind
  . induction h
    case base a b h => grind
    case step a b c h₁ h₂ ih => grind


lemma trans_idem (R : A → A → Prop) :
  trans_clos (trans_clos R) = trans_clos R := by
    funext x y; apply propext; constructor
    case _ =>
      intros h; induction h
      case _ => grind
      case _ a b c h₁ h₂ h₃ =>
        -- This is still awkward because of the type class stuff
        have h := @trans_clos_transitive _ ⟨R⟩
        apply h a b c <;> simp <;> grind
    case _ =>
      intros h; induction h
      case _ => grind
      case _ a b c h₁ h₂ h₃ =>
        have h := @trans_clos_transitive _ ⟨trans_clos R⟩
        apply h a b c <;> simp <;> grind


@[simp]
lemma refl_sym_is_sym_refl (R : A → A → Prop) :
  refl_clos (sym_clos R) = sym_clos (refl_clos R)
  := by funext x y; grind

lemma refl_trans_sym_is_trans_sym_refl (R : A → A → Prop) :
  refl_clos (trans_clos (sym_clos R)) = trans_clos (sym_clos (refl_clos R)) := by
  funext x y; apply propext; constructor <;> intros h
  . induction h
    case _ => grind
    case _ z ih =>
      apply trans_clos_monotone
      . apply sym_clos_monotone (R := R); intros x y r; grind
      . trivial
  . induction h <;> grind

lemma trans_is_refl_trans [R : Red A] {x y : A} : x ~>+ y → x ~>* y :=
by
  simp
  intros red
  induction red
  . apply refl_trans_clos.step; trivial
    constructor
  . case step red _ ih => grind

lemma refl_trans_is_trans_or_eq [R : Red A] {x y : A} : x ~>* y → x = y ∨ x ~>+ y :=
by
  simp
  intros red
  induction red <;> grind

@[grind =>]
lemma refl_trans_step_is_trans [R : Red A] : ∀ x y z : A, x ~> z → z ~>* y → x ~>+ y :=
by
  simp
  intros x y z red_x_z red_z_y
  revert red_x_z x
  induction red_z_y <;> grind

lemma sym_inv (R : A → A → Prop) : R⁻¹ ≤ sym_clos R :=
 by intros x y; simp [Inv.inv]; grind

def diverge_from [R : Red A] (x : A) : Prop :=
  ∃ xs : Nat → A, xs 0 = x ∧ ∀ n, xs n ~> xs (n+1)

def normalizes [R : Red A] (x : A) : Prop := ¬ (diverge_from x)

@[grind]
def normalizing (R : Red A) : Prop := ∀ x : A, normalizes x

@[grind]
def normal [R : Red A] (x : A) : Prop := ¬ (∃ x', x ~> x')

theorem normal_normalizing [R : Red A] {x : A} : normal x → normalizes x :=
by
  simp [normal]
  intros norm_x div_x
  match div_x with
  | .intro _ _ => grind

-- An alternate way to define normality.
lemma normal_red [R : Red A] {x y : A} : normal x → x ~>* y → x = y :=
by
  intros norm red
  cases red ; trivial
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
  cases ex_t; grind

#print Classical.axiomOfChoice

theorem iterate_left {A} (f : A → A) (n : ℕ) (x : A) : f^[n+1] x = f (f^[n] x) := by
  simp [Nat.iterate]
  revert x
  induction n <;> grind [Nat.iterate]

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
       apply And.intro <;> grind [Nat.iterate, iterate_left]

-- So tedious!
lemma dependent_choice : ∀ {A}
  (Q : A → A → Prop),
  Inhabited A →
  (∀ a, ∃ b, Q a b) →
  ∃ f : ℕ → A, ∀ n, Q (f n) (f (n+1)) :=
by
  intros A Q inhab forall_exists_Q
  have a : A := inhab.default
  have h := dependent_choice' _ a forall_exists_Q
  cases h
  case intro f h' =>
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
    cases ap
    simp; grind
  match h with
  | .intro f _ =>
    exists (λ n ↦ (f n).val)
    grind

-- This is the "real" def of normalization, or at least the
-- one that's actually useful.
lemma normalizes_ind [R : Red A] : ∀ P : A → Prop,
  (∀ x, (∀ y, x ~> y → P y) → P x) → ∀ x, normalizes x → P x :=
by
  intros P IH x norm
  apply Classical.byContradiction
  intro h; apply norm
  have h' : ∃ f : ℕ → A, f 0 = x ∧ ∀ n, ¬ P (f n) ∧ f n ~> f (n+1) :=
  by
    apply (dependent_choice''  (λ a ↦ ¬ P a)) <;> grind
  rw [diverge_from]
  match h' with
  | Exists.intro xs _ =>
    exists xs; grind


lemma normalizing_ind [R : Red A] : ∀ P : A → Prop,
  (∀ x, (∀ y, x ~> y → P y) → P x) → normalizing R → ∀ x, P x :=
by
  intros P IH norm x
  apply normalizes_ind
  . apply IH
  . apply norm


lemma ind_normalizing [R : Red A] :
   (∀ P : A → Prop, (∀ x, (∀ y, x ~> y → P y) → P x) → ∀ x, P x) → normalizing R :=
by
  intros ih x
  apply ih
  intros x red_norm div
  cases div
  case _ f h =>
    apply red_norm
    . simp [← h.1]
      apply h.2 0
    . exists (λ n ↦ f (n+1))
      grind

@[grind .]
lemma red_ref_trans_clos [R : Red A] : ∀ x y z : A, x ~> y → y ~>* z → x ~>* z :=
by
  simp; intros x y z red_x_y h ; grind

lemma normalizing_normal [R : Red A] (x : A) : normalizes x → ∃ y : A, x ~>* y ∧ normal y := by
  revert x; apply normalizes_ind
  intros x ih
  by_cases h : (∃ y, x ~> y)
  case pos =>
    let ⟨y', red⟩ := h
    let ⟨z, red, nf⟩ := (ih y' red)
    exists z ; grind
  case neg => exists x ; simp at *; grind [normal]

def joins [R : Red A] := λ x y ↦ ∃ z : A, x ~>* z ∧ y ~>* z

def wedge [R : Red A] : A → A → Prop := λ (u v : A) ↦ ∃ t, t ~>* u ∧ t ~>* v

infix:50 " ~>*.*<~ " => joins
infix:50 " *<~.~>* " => wedge

def church_rosser (R : Red A) := ∀ (x y : A), x <~>* y → x ~>*.*<~ y

def confluent (R : Red A) := ∀ (y z : A), y *<~.~>* z → y ~>*.*<~ z

def diamond (R : Red A) :=
  ∀ x y z : A, x ~> y → x ~> z → ∃ w, y ~> w ∧ z ~> w

def weakly_confluent (R : Red A) :=
  ∀ x y z : A, x ~> y → x ~> z → y ~>*.*<~ z

def semi_confluent (R : Red A) :=
  ∀ x y z : A, x ~> y → x ~>* z → y ~>*.*<~ z

-- let's relate all of these

@[grind .]
lemma refl_trans_sym_refl_trans (R : A → A → Prop) :
  refl_trans_clos R ≤ refl_trans_sym_clos R :=
by
  simp [LE.le]
  intros x y red
  induction red <;> grind

lemma wedge_inc_refl_sym_trans [R : Red A] : wedge (R:=R) ≤ refl_trans_sym_clos R.reduces := by
  intros x y; simp [wedge]; intros z
  intros; apply refl_trans_sym_clos.trans x z y
  case _ => apply refl_trans_sym_clos.inv; apply refl_trans_sym_refl_trans; trivial
  case _ => apply refl_trans_sym_refl_trans; trivial

-- this one is trivial
lemma church_rosser_implies_confluent [R : Red A] : church_rosser R → confluent R :=
  by
    intros cr y z wedge
    have h : y <~>* z := by apply wedge_inc_refl_sym_trans; trivial
    apply cr
    trivial

-- quite useful manipulations
@[grind →]
lemma swap_joins [R : Red A] : ∀ x y : A, x ~>*.*<~ y → y ~>*.*<~ x := by
  intros x y joins_x_y
  grind [joins]

lemma red_joins [R : Red A] : ∀ x y z : A, x ~> y → y ~>*.*<~ z → x ~>*.*<~ z := by
  intros x y z red_x_y joins_y_z
  grind [joins]

@[grind →]
lemma reds_joins_left [R : Red A] : ∀ x y z : A, x ~>* y → y ~>*.*<~ z → x ~>*.*<~ z := by
  intros x y z red_x_y joins_y_z
  induction red_x_y <;> grind [red_joins]

@[grind →]
lemma reds_joins_right [R : Red A] : ∀ x y z : A, x ~>* z → y ~>*.*<~ z → y ~>*.*<~ x :=
by
  intros x y z red_x_y joins_y_z
  grind [swap_joins, reds_joins_left]

-- this one is surprising, but not too tough.
lemma semi_confluent_implies_confluent [R : Red A] : semi_confluent (R:=R) → confluent (R:=R) := by
  intros sc x y wdg
  have ⟨t, h₁, h₂⟩ := wdg
  revert wdg h₂ y
  induction h₁
  case _ w =>
    intros y h₁ h₂
    exists y; simp at *; grind
  case _ a b c h₃ h₄ ih =>
    intros y wdg red_a_y
    unfold semi_confluent at sc
    have h₅ := sc a b y (by trivial) (by trivial)
    have ⟨w, h₅, h₆⟩ := h₅
    -- now we're in place for IH
    have h₇ := ih w ⟨b, by trivial, by trivial⟩ (by trivial)
    have ⟨w', h₇, h₈⟩ := h₇
    grind


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
  case _ _ =>
    intros y _; exists y ; simp at *; grind
  case _ a b c red_a_b red_b_c ih =>
    intros y red_a_y
    have ⟨w, h₁, h₂⟩ := sc a y b (by trivial) (by trivial)
    have ⟨w', _, _⟩ := ih w h₂
    exists w'; grind

-- also trivial
lemma confluent_implies_weakly_confluent : confluent R → weakly_confluent R :=
by
  intros confl x y z red_x_y red_x_z
  apply confl; exists x; constructor <;> apply refl_trans_clos.step <;> try constructor
  . trivial
  . trivial

-- this one is a little more work.
-- again, something clear from a diagram requires a somewhat tedious mechanical proof
lemma confluent_implies_church_rosser : confluent R → church_rosser R := by
  intros conf y z equiv_y_z
  induction equiv_y_z
  case trans a b c _ _ h₁ h₂ =>
    have ⟨w₁, _, _⟩ := h₁
    have ⟨w₂, _, _⟩ := h₂
    have ⟨w₃, _, _⟩ := conf w₁ w₂ ⟨b, by trivial, by trivial⟩
    exists w₃
    grind [refl_trans_clos_transitive]
  case inv a b _ h => grind
  case refl a => exists a; simp; grind
  case base a b _ => exists b; simp; grind

-- Weakly confluent does not imply confluent in general!
inductive X where | a | b | c | d

-- a <- b <=> c -> d

-- This definition is a bit tedious because of dependent matching.
/- inductive RX : X → X → Prop :=
  | r_b_a : RX b a
  | r_b_c : RX b c
  | r_c_b : RX c b
  | r_c_d : RX c d
 -/
-- This one works great with simp and friends
@[grind]
def RX : X → X → Prop :=
  open X in
  fun x y ↦
    (x = b ∧ y = a)
  ∨ (x = b ∧ y = c)
  ∨ (x = c ∧ y = b)
  ∨ (x = c ∧ y = d)

instance redX : Red X := ⟨RX⟩

lemma not_joins_a_d : ¬ joins X.a X.d := by
  simp [joins, reduces]; grind


lemma weakly_confluent_does_not_imply_confluent : ∃ (A : Type) (R : Red A),
weakly_confluent R ∧ ¬ confluent R :=
by
  exists X, ⟨RX⟩
  constructor
  . intros x y z r_x_y r_x_z
    simp [RX] at r_x_y
    simp [RX] at r_x_z
    -- ugh this is tedious. Probably there's some nuclear tactic here (grind?)
    cases r_x_y <;> cases r_x_z <;> simp [*] at *
    . exists X.a; simp; grind
    . exists X.a; try constructor
      . constructor
      . simp [*]; constructor; simp [RX]
        . left; trivial
        . constructor; unfold RX; left; trivial; constructor
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
      . unfold RX
        left; trivial
      . constructor
    . simp
      apply refl_trans_clos.step X.b X.c X.d; unfold RX; grind
      apply refl_trans_clos.step X.c X.d X.d; unfold RX; grind
      apply refl_trans_clos.refl


inductive close_below (P : A → Prop) : A → Prop where
  | here : ∀ x, P x → close_below P x

-- Sometimes it's easier to work with the transitive closure for WF induction.
lemma normalizes_trans [R : Red A] : normalizing R → normalizing (R := ⟨trans_clos R.reduces⟩) :=
by
  intros norm
  apply ind_normalizing (R := ⟨trans_clos (R.reduces)⟩)
  intros P ih
  let Q := λ x ↦ P x ∧ ∀ y, x ~>+ y → P y
  have h : ∀ x, Q x :=
  by
    intros x
    apply normalizing_ind
    case _ => simp [Q]; grind
    case _ => trivial
  grind

-- When proving confluence, it's sometimes tedious to always handle the reflexive case.
def confluent' [R : Red A] := ∀ x y z : A, x ~>+ y → x ~>+ z → y ~>*.*<~ z

lemma confluent'_implies_confluent : confluent' (R:=R) → confluent R :=
by
  intros conf'
  apply semi_confluent_implies_confluent
  intros x y z red_x_y red_x_z
  have h := refl_trans_is_trans_or_eq red_x_z
  cases h
  . case a.inl h =>
    simp [← h]
    exists y ; simp; grind
  . apply conf' x y z <;> simp at * <;> grind

-- but if R is normalizing...
theorem newmans_lemma : normalizing R → weakly_confluent R → confluent R :=
  -- Requires a clever induction on diagrams
by
  intros norm_R weak
  intros y z wedge
  cases wedge
  case intro x h =>
  revert h z y
  have norm_trans := normalizes_trans norm_R
  have h :=
    normalizes_ind (R := ⟨trans_clos R.reduces⟩)
    (λ x ↦ ∀ y z, x ~>* y ∧ x ~>* z → y ~>*.*<~ z)
  intros y z wedge
  (apply h <;> try trivial) <;> try apply norm_trans
  clear h
  intros x ih y z wedge
  cases wedge.1
  . exists z; simp at *; grind
  . case a.step y' red_x_y' red_y'_y =>
    cases wedge.2
    . exists y; simp at *; grind
    . case step z' red_x_z' red_z'_z =>
      -- finally use weak confluence
      have ⟨w₁, _, _⟩ := weak _ _ _ red_x_y' red_x_z'
      have ⟨w₂, _, _⟩ := ih y' (by grind) y w₁ (by trivial)
      have ⟨w₃, _ , _⟩ := ih z' (by grind) z w₁ (by trivial)
      have h : x ~>+ w₁ := by grind
      have ⟨w₄, _, _⟩ := ih w₁ h w₁ w₂ (by simp at *; grind)
      grind

lemma confluent_unique_nf [R : Red A] : confluent R →
  ∀ x y z : A, x ~>* y → x ~>* z → normal y → normal z → y = z := by
  intros conf x y z red_x_y red_x_z nf_y nf_z
  have ⟨w, h₁, h₂⟩ := conf y z ⟨x, by trivial, by trivial⟩
  simp at *; grind

section Commuting

class Red₁ (A : Type) where
  reduces (x y : A) : Prop

def Red₁.toRed (R : Red₁ A) : Red A := ⟨R.reduces⟩

class Red₂ (A : Type) where
  reduces (x y : A) : Prop

def Red₂.toRed (R : Red₂ A) : Red A := ⟨R.reduces⟩

infixl:50 " ~>₁ " => Red₁.reduces
infixl:50 " ~>₂ " => Red₂.reduces

@[simp]
def refl_trans_clos_red₁ [R : Red₁ A] := refl_trans_clos R.reduces

@[simp]
def refl_trans_clos_red₂ [R : Red₂ A] := refl_trans_clos R.reduces

infixl:50 " ~>₁* "   => refl_trans_clos_red₁
infixl:50 " ~>₂* "   => refl_trans_clos_red₂

def union (R R' : A → A → Prop) : A → A → Prop :=
  fun x y => R x y ∨ R' x y

def unionRed [R : Red₁ A] [R' : Red₂ A] := union R.reduces R'.reduces

infix:50 " ~>₁+~>₂ " => unionRed

-- This is a pretty powerful property: basically you can do ~>₁ and ~>₂ reductions
-- in *any* order you like.
def commutes (R : Red₁ A) (R' : Red₂ A) := ∀ x y z : A, x ~>₁* y → x ~>₂* z →
  ∃ w, y ~>₂* w ∧ z ~>₁* w

-- Obviously the transitive closure of the union contains the union of transitive
-- closures.
lemma trans_union_leq_union_trans (R R' : A → A → Prop) :
  union (trans_clos R) (trans_clos R') ≤ trans_clos (union R R') := by
  intros a b h
  cases h
  case _ =>
    apply trans_clos_monotone (R := R) <;> try trivial
    intros a b; simp [LE.le, union]; grind
  case _ =>
    apply trans_clos_monotone (R := R') <;> try trivial
    intros a b; simp [LE.le, union]; grind

def comp (R R' : A → A → Prop) : A → A → Prop := fun x y => ∃ z, R x z ∧ R' z y

@[simp]
def compRed [R : Red₁ A] [R' : Red₂ A] := comp R.reduces R'.reduces

infix:50 " ~>₁;~>₂ " => compRed

lemma contains_and_contained_trans_implies_trans_equal (R R' : A → A → Prop) :
  R ≤ R' → R' ≤ refl_trans_clos R → refl_trans_clos R' = refl_trans_clos R := by
  intros le₁ le₂
  funext x y; apply propext; constructor
  . intros h
    induction h
    case refl => grind
    case step a b c h₁ h₂ ih =>
      have : refl_trans_clos R a b := by
        apply le₂; trivial
      grind
  . apply refl_trans_clos_monotone; trivial

lemma contains_and_contained_trans_implies_diamond_conf
  [R : Red₁ A]
  [R' : Red₂ A] :
  R.reduces ≤ R'.reduces → R'.reduces ≤ refl_trans_clos R.reduces → diamond R'.toRed → confluent R.toRed := by
    intros h₁ h₂
    have h := contains_and_contained_trans_implies_trans_equal _ _ h₁ h₂
    intros diamond'
    have h' := diamond_implies_confluent diamond'
    have : confluent R'.toRed = confluent R.toRed := by
      simp [Red₁.toRed, Red₂.toRed, confluent, wedge, joins]
      rw [h]
    grind

end Commuting

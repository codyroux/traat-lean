import Traat.chapter3
import Mathlib.Data.Finset.Max

section Position

inductive Move where | left | right
  deriving BEq, Repr

open Move Term

-- A position in a term is just a sequence of moves to a "head" position.
abbrev Position := List Move

def Position.valid (p : Position) (t : Term) : Bool :=
  match p, t with
  | [], _ => true
  | left::ps, t₁ @@ _ => Position.valid ps t₁
  | right::ps, _ @@ t₂ => Position.valid ps t₂
  | _::_, _ => false

def Position.get (p : Position) (t : Term) (h : p.valid t) : Term :=
  match p, t with
  | [], _ => t
  | left::ps, t₁ @@ _ => Position.get ps t₁ h
  | right::ps, _ @@ t₂ => Position.get ps t₂ h
  | _::_, _ => t

#eval ("f" @@ var "x" @@ var "y")

#eval let p : Position := [left, left]
  p.get ("f" @@ var "x" @@ var "y") (refl true)


def Position.get? (p : Position) (t : Term) : Option Term :=
  match p, t with
  | [], _ => t
  | left::ps, t₁ @@ _ => Position.get? ps t₁
  | right::ps, _ @@ t₂ => Position.get? ps t₂
  | _::_, _ => none

abbrev Position.head : Position := []

@[simp, grind .]
lemma Position.eq_head_of_valid_var (h : p.valid (var x)) : p = Position.head := by
  revert h; induction p <;> grind only [valid]

@[simp, grind .]
lemma Position.eq_head_of_valid_func (h : p.valid (func x)) : p = Position.head := by
  revert h; induction p <;> grind only [valid]


lemma Position.valid_apply {p : Position} {t : Term} (σ : Subst)
  (h : p.valid t)
  : p.valid <| t.apply σ := by
  match p, t with
  | [], _ => simp only [valid]
  | left::ps, t₁ @@ t₂ =>
    simp only [apply, valid]; apply Position.valid_apply
    . simp only [valid] at h; trivial
  | right::ps, t₁ @@ t₂ =>
    simp only [apply, valid]; apply Position.valid_apply
    . simp only [valid] at h; trivial
  | _::_, var _ => simp only [valid, Bool.false_eq_true] at h
  | _::_, func _ => simp only [valid, Bool.false_eq_true] at h

lemma Position.valid_append_left {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : p₁.valid t := by
  revert h
  match p₁, t with
  | [], _ => simp [Position.valid]
  | left::_, t₁ @@ _ => simp only [List.cons_append, valid]; intro h; apply Position.valid_append_left h
  | right::_, _ @@ t₂ => simp only [List.cons_append, valid]; intro h; apply Position.valid_append_left h
  | _::_, var _ => simp only [List.cons_append, valid, Bool.false_eq_true, imp_self]
  | _::_, func _ => simp only [List.cons_append, valid, Bool.false_eq_true, imp_self]

lemma Position.valid_append_right {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : p₂.valid <| p₁.get t (Position.valid_append_left h) := by
  revert h
  match p₁, t with
  | [], _ => simp only [List.nil_append, get, imp_self]
  | left::_, t₁ @@ _ => simp only [List.cons_append, valid, get]; intro h; apply Position.valid_append_right h
  | right::_, _ @@ t₂ => simp only [List.cons_append, valid, get]; intro h; apply Position.valid_append_right h
  | _::_, var _ => simp only [List.cons_append, valid, Bool.false_eq_true, IsEmpty.forall_iff]
  | _::_, func _ => simp only [List.cons_append, valid, Bool.false_eq_true, IsEmpty.forall_iff]

@[simp]
lemma Position.get_append {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : (p₁ ++ p₂).get t h = p₂.get (p₁.get t <| Position.valid_append_left h) (Position.valid_append_right h) := by
  revert h
  match p₁, t with
  | [], _ => simp [Position.valid, Position.get]
  | left::_, t₁ @@ _ => simp only [List.cons_append, valid, get]; intro h; apply Position.get_append h
  | right::_, _ @@ t₂ => simp only [List.cons_append, valid, get]; intro h; apply Position.get_append h
  | _::_, var _ => simp only [List.cons_append, valid, Bool.false_eq_true, IsEmpty.forall_iff]
  | _::_, func _ => simp only [List.cons_append, valid, Bool.false_eq_true, IsEmpty.forall_iff]

-- define splitting of a position in tσ into a position in t and a "tail"
-- prove that the concat is the original path
def Position.splitOnSubst (p : Position) (t : Term) (σ : Subst) : Position × Position :=
  match p, t with
  | _, var _ => ([], p)
  | _, func _ => ([], p)
  | left::p', t₁ @@ _ =>
    let (p₁, p₂) := Position.splitOnSubst p' t₁ σ
    (left::p₁, p₂)
  | right::p', _ @@ t₂ =>
    let (p₁, p₂) := Position.splitOnSubst p' t₂ σ
    (right::p₁, p₂)
  | [], _ => ([], [])

@[simp]
lemma Position.splitOnSubst_head : Position.splitOnSubst [] t σ = ([], []) := by
  induction t <;> simp only [splitOnSubst]

lemma Position.splitOnSubst_fst_valid {p : Position} (h : p.valid (t.apply σ))
  : (p.splitOnSubst t σ).fst |>.valid t := by
  revert h
  match p, t with
  | [], _ => simp [Position.valid]
  | left::p', t₁ @@ _ =>
    simp only [apply, valid, splitOnSubst]
    intros; apply Position.splitOnSubst_fst_valid; grind only
  | right::p', _ @@ t₂ =>
    simp only [apply, valid, splitOnSubst]
    intros; apply Position.splitOnSubst_fst_valid; grind only
  | _, var _ =>
    simp only [apply, splitOnSubst, valid, implies_true]
  | _, func _ =>
    simp only [apply, splitOnSubst, valid, implies_true]

lemma Position.splitOnSubst_concat {p : Position}
 : (p.splitOnSubst t σ).1 ++ (p.splitOnSubst t σ).2 = p := by
  match p, t with
  | [], _ => simp only [splitOnSubst_head, List.append_nil]
  | left::p', t₁ @@ _ =>
    simp only [splitOnSubst, List.cons_append, List.cons.injEq, true_and]
    apply Position.splitOnSubst_concat
  | right::p', _ @@ t₂ =>
    simp only [splitOnSubst, List.cons_append, List.cons.injEq, true_and]
    apply Position.splitOnSubst_concat
  | _, var _ =>
    simp only [splitOnSubst, List.nil_append]
  | _, func _ =>
    simp only [splitOnSubst, List.nil_append]

-- A rewrite at a position that satisfies this predicate is "outer", that is
-- it occurs only within substituted terms.
def IsOuterPosition (p : Position) (t : Term) (σ : Subst) : Bool :=
  let ⟨p, _⟩ := p.splitOnSubst t σ
  if h : (p.valid t) then p.get t h |>.isVar else false

lemma IsOuterPosition.exists_split (h : IsOuterPosition p t σ) :
  ∃ (p₁ p₂ : Position) (x : Var) (h₁ : p₁.valid t),
    p = p₁ ++ p₂ ∧ p₁.get t h₁ = var x := by
  revert h t
  induction p
  case _ =>
    simp only [IsOuterPosition, Position.valid, Position.splitOnSubst_head, ↓reduceDIte,
      List.nil_eq, List.append_eq_nil_iff, exists_and_left, exists_and_right, ↓existsAndEq,
      and_true, exists_eq_left, exists_true_left]
    intros t; cases t <;> grind only [isVar, Position.get]
  case _ hd tail ih =>
    intros t
    cases t
    case var y =>
      intros _
      exists [], (hd::tail), y, (Eq.refl true)
    case func _ =>
      simp only [IsOuterPosition, Position.splitOnSubst, Position.valid, ↓reduceDIte, isVar,
        Position.get, Bool.false_eq_true, exists_and_left, exists_and_right, IsEmpty.forall_iff]
    case app t₁ t₂ =>
      cases hd
      case _ =>
        intros h
        have h' : IsOuterPosition tail t₁ σ := by exact h
        have ⟨p₁, ⟨p₂, ⟨y, ⟨h₁, _⟩⟩⟩⟩ := ih h'
        exists (left::p₁), p₂, y, h₁
        simp only [List.cons_append, List.cons.injEq, true_and, Position.get]; grind only
      case _ =>
        intros h
        have h' : IsOuterPosition tail t₂ σ := by exact h
        have ⟨p₁, ⟨p₂, ⟨y, ⟨h₁, _⟩⟩⟩⟩ := ih h'
        exists (right::p₁), p₂, y, h₁
        simp only [List.cons_append, List.cons.injEq, true_and, Position.get]; grind only

-- define subst-at, rewrite-at, prove that you can always replace a rewrite with a rewrite at

def Term.substAt (t : Term) (p : Position) (h : p.valid t) (u : Term) : Term :=
match p, t with
| [], _ => u
| left::p', t₁ @@ t₂ => (Term.substAt t₁ p' h u) @@ t₂
| right::p', t₁ @@ t₂ => t₁ @@ (Term.substAt t₂ p' h u)
| _::_, var _ => by simp only [Position.valid, Bool.false_eq_true] at h
| _::_, func _ => by simp only [Position.valid, Bool.false_eq_true] at h

lemma Term.substAt_valid_aux {p : Position} (h : p.valid t)
  : p.valid (t.substAt p h u) := by
  revert h
  match p, t with
  | [], _ => simp only [Position.valid, imp_self]
  | left::p', t₁ @@ _ =>
    simp only [Position.valid, substAt]
    apply Term.substAt_valid_aux
  | right::p', _ @@ t₂ =>
    simp only [Position.valid, substAt]
    apply Term.substAt_valid_aux
  | _::_, var _ => simp only [Position.valid, Bool.false_eq_true, substAt, IsEmpty.forall_iff]
  | _::_, func _ => simp only [Position.valid, Bool.false_eq_true, substAt, IsEmpty.forall_iff]

@[simp]
lemma Position.get_substAt_of_valid {t : Term} {p : Position}
 (h : p.valid t)
 (h' : p.valid (t.substAt p h u))
 : p.get (t.substAt p h u) h' = u := by
  revert h
  match p, t with
  | [], _ => simp only [valid, get, substAt, imp_self]
  | left::p', t₁ @@ _ =>
    simp only [valid, substAt]
    apply Position.get_substAt_of_valid
  | right::p', _ @@ t₂ =>
    simp only [valid, substAt]
    apply Position.get_substAt_of_valid
  | _::_, var _ => simp only [valid, Bool.false_eq_true, substAt, IsEmpty.forall_iff]
  | _::_, func _ => simp only [valid, Bool.false_eq_true, substAt, IsEmpty.forall_iff]

lemma Position.get_substAt {t : Term} {p : Position} (h : p.valid t)
 : p.get (t.substAt p h u) (Term.substAt_valid_aux h) = u := by
 simp

def Position.Inc (p q : Position) : Bool :=
match p, q with
| [], _ => true
| left::p', left::q' => Position.Inc p' q'
| right::p', right::q' => Position.Inc p' q'
| _, _ => false

instance Position.instHasSubset : HasSubset Position where
  Subset p q := Position.Inc p q

@[simp]
lemma Position.empty_subset {p : Position} : [] ⊆ p := by
  simp only [Subset, Inc]

@[simp]
lemma Position.not_cons_subset_empty {p : Position} : ¬ m::p ⊆ [] := by
  simp only [Subset, Inc, Bool.false_eq_true, not_false_eq_true]

@[simp]
lemma Position.cons_subset_cons_iff {p q : Position} : (m::p ⊆ m::q) = (p ⊆ q) := by
  cases m
  . match p, q with
    | [], _ => simp only [Subset, Position.Inc]
    | left::p', left::q' => simp only [Subset, Position.Inc]
    | right::p', right::q' => simp only [Subset, Position.Inc]
    | _, _ => simp only [Subset, Position.Inc]
  . match p, q with
    | [], _ => simp only [Subset, Position.Inc]
    | left::p', left::q' => simp only [Subset, Position.Inc]
    | right::p', right::q' => simp only [Subset, Inc]
    | _, _ => simp only [Subset, Inc]

@[grind .]
lemma Position.not_cons_subset_cons_of_ne {p q : Position} (h : m ≠ n) : ¬ (m::p ⊆ n::q) := by
  revert h
  cases m <;> cases n
  . simp only [ne_eq, not_true_eq_false, Subset, Inc, Bool.not_eq_true, IsEmpty.forall_iff]
  . simp only [ne_eq, reduceCtorEq, not_false_eq_true, Subset, Inc, Bool.false_eq_true, imp_self]
  . simp only [ne_eq, reduceCtorEq, not_false_eq_true, Subset, Inc, Bool.false_eq_true, imp_self]
  . simp only [ne_eq, not_true_eq_false, Subset, Inc, Bool.not_eq_true, IsEmpty.forall_iff]

-- A little tedium here
@[grind →]
lemma Position.valid_of_valid_of_subset {p q : Position} (h : q.valid t) (inc : p ⊆ q)
 : p.valid t := by
  revert inc h; simp only [Subset]
  match p, q, t with
  | [], _, _ => simp only [valid, implies_true]
  | left::p', left::q', t₁ @@ _ =>
    simp only [valid, Inc]
    apply Position.valid_of_valid_of_subset
  | right::p', right::q', _ @@ t₂ =>
    simp only [valid, Inc]
    apply Position.valid_of_valid_of_subset
  | _, _::_, var _ => simp only [valid, Bool.false_eq_true, IsEmpty.forall_iff]
  | _, _::_, func _ => simp only [valid, Bool.false_eq_true, IsEmpty.forall_iff]
  | _::_, [], _ => simp only [Inc, Bool.false_eq_true, IsEmpty.forall_iff, implies_true]
  | right::_, left::_, _ => simp only [Inc, Bool.false_eq_true, IsEmpty.forall_iff, implies_true]
  | left::_, right::_, _ => simp only [Inc, Bool.false_eq_true, IsEmpty.forall_iff, implies_true]

def Position.sdiff (p q : Position) : Position :=
  match p, q with
  | _, [] => p
  | [], _ => []
  | left::p', left::q' => Position.sdiff p' q'
  | right::p', right::q' => Position.sdiff p' q'
  | _, _ => p

instance Position.instSDiff : SDiff Position where
  sdiff := Position.sdiff

@[simp]
lemma Position.sdiff_empty_right {p : Position} : p \ [] = p := by
  induction p <;> simp only [SDiff.sdiff, sdiff]

@[simp]
lemma Position.empty_sdiff {p : Position} : [] \ p = [] := by
  induction p <;> simp only [SDiff.sdiff, sdiff]

@[simp]
lemma Position.sdiff_cons_cons {p q : Position} {m : Move} : (m::p) \ (m::q) = p \ q := by
  cases m <;> simp only [SDiff.sdiff, sdiff]

@[simp]
lemma Position.sdiff_self {p : Position} : (p \ p) = [] := by
  induction p <;> simp only [sdiff_empty_right, sdiff_cons_cons]; trivial

lemma Position.eq_append_sdiff_of_subset {p q : Position} (inc : p ⊆ q) : q = p ++ (q \ p) := by
  revert inc
  cases p <;> cases q
  case _ => simp only [empty_subset, sdiff_self, List.append_nil, imp_self]
  case _ => simp only [empty_subset, sdiff_empty_right, List.nil_append, imp_self]
  case _ => simp only [not_cons_subset_empty, empty_sdiff, List.append_nil, List.nil_eq,
    reduceCtorEq, imp_self]
  case cons.cons m _ n _ =>
    simp only [List.cons_append, List.cons.injEq]
    by_cases h:(m = n)
    . simp only [h, cons_subset_cons_iff, sdiff_cons_cons, true_and]; apply Position.eq_append_sdiff_of_subset
    . grind only [not_cons_subset_cons_of_ne]

def Position.IsOrtho (p q : Position) : Bool :=
  match p, q with
  | left::_, right::_ => true
  | right::_, left::_ => true
  | left::p', left::q'
  | right::p', right::q' => Position.IsOrtho p' q'
  | _, _ => false

infix:50 " ⊥ " => Position.IsOrtho

@[grind =]
lemma Position.isOrtho_cons_of_ne (h : m ≠ n) : (m::p) ⊥ (n::q) := by
  revert h; cases m <;> cases n <;> simp only [ne_eq, not_false_eq_true, not_true_eq_false, IsOrtho, IsEmpty.forall_iff, reduceCtorEq, imp_self]

@[simp]
lemma Position.isOrtho_cons_iff : ((m::p) ⊥ (m::q)) = (p ⊥ q) := by
  cases m <;> simp only [IsOrtho]

@[grind .]
lemma Position.not_isOrtho_nil_left : ¬ ([] ⊥ p) := by
  cases p <;> simp only [IsOrtho, Bool.false_eq_true, not_false_eq_true]

@[grind .]
lemma Position.not_isOrtho_nil_right : ¬ (p ⊥ []) := by
  cases p <;> simp only [IsOrtho, Bool.false_eq_true, not_false_eq_true]

lemma Position.trichotomy (p q : Position) : p ⊆ q ∨ q ⊆ p ∨ p ⊥ q := by
  cases p <;> cases q <;> try simp only [empty_subset, not_cons_subset_empty, false_or, true_or]
  case cons.cons m _ n _ =>
    by_cases h:(m = n)
    . simp only [h, cons_subset_cons_iff, isOrtho_cons_iff]; apply Position.trichotomy
    . grind only [= isOrtho_cons_of_ne]

lemma Position.isOrtho_comm {p q : Position} (h : p ⊥ q) : q ⊥ p := by
  revert h
  match p, q with
  | [], _ => simp only [IsOrtho, Bool.false_eq_true, imp_self]
  | _::_, [] => simp only [IsOrtho, Bool.false_eq_true, imp_self]
  | left::_, left::_ => simp only [IsOrtho]; apply Position.isOrtho_comm
  | right::_, right::_ => simp only [IsOrtho]; apply Position.isOrtho_comm
  | left::_, right::_ => simp only [IsOrtho, imp_self]
  | right::_, left::_ => simp only [IsOrtho, imp_self]

end Position

open Position Move Term

-- This is a compbination of `Reduces.apply` and `Reduces.ax`.
@[simp]
def Rule.matchesHead (r : Rule) (t : Term) (σ : Subst) : Prop :=
  r.lhs.apply σ = t

-- Hey we don't even need the term here!
@[simp]
def Rule.rewriteHead (r : Rule) (σ : Subst) : RTerm ℛ := r.rhs.apply σ

-- A little awkward to have to bundle the `p.valid t` proof here.
def Rule.matchesAt (r : Rule) (t : Term) (p : Position) (σ : Subst) (h : p.valid t) : Prop :=
  r.matchesHead (p.get t h) σ

def Rule.rewriteAt
  (r : Rule)
  (t : RTerm ℛ)
  (p : Position)
  (σ : Subst) (h : p.valid t) : RTerm ℛ :=
  t.substAt p h (r.rewriteHead (ℛ:=ℛ) σ)

-- This is our master theorem to move between the "nice" definition of rewriting to the
-- position based one, which will allow us to do horrible reasoning about critical pairs.
theorem Reduces.exists_rewriteAt {ℛ : Rules} (t t' : RTerm ℛ) (red : t ~> t')
 : ∃ r ∈ ℛ, ∃ (p : Position) (σ : Subst) (h : p.valid t),
  r.matchesAt t p σ h ∧ t' = r.rewriteAt t p σ h := by
  simp [Red.reduces] at red
  induction red
  case _ l r σ mem =>
    exists ⟨l, r⟩; apply And.intro; trivial
    exists []; exists σ; exists rfl
    simp only [Rule.matchesAt, Rule.matchesHead, Position.get, Rule.rewriteAt, Rule.rewriteHead,
      substAt, and_self]
  case _ ih =>
    let ⟨r, ⟨mem, ⟨p, ⟨σ, ⟨h, eq⟩⟩⟩⟩⟩ := ih
    exists r; apply And.intro; trivial
    exists (left::p); exists σ; exists h
    simp only [Rule.rewriteAt, substAt, Rule.rewriteHead, app.injEq, and_true]
    simp only [Rule.rewriteAt, Rule.rewriteHead] at eq
    trivial
  case _ ih =>
    let ⟨r, ⟨mem, ⟨p, ⟨σ, ⟨h, eq⟩⟩⟩⟩⟩ := ih
    exists r; apply And.intro; trivial
    exists (right::p); exists σ; exists h
    simp only [Rule.rewriteAt, substAt, Rule.rewriteHead, app.injEq, true_and]
    simp only [Rule.rewriteAt, Rule.rewriteHead] at eq
    trivial

@[simp]
lemma Term.substAt_valid {t : Term} {p : Position}
  (h : p.valid t)
  : p.valid (t.substAt p h u) := by
  revert h
  match p, t with
  | [], _ => simp only [valid, imp_self]
  | left::_, _ @@ _ => simp only [valid, substAt]; apply Term.substAt_valid
  | right::_, _ @@ _ => simp only [valid, substAt]; apply Term.substAt_valid
  | left::_, var _ => simp only [valid, Bool.false_eq_true, IsEmpty.forall_iff]
  | right::_, var _ => simp only [valid, Bool.false_eq_true, reduceCtorEq, imp_self, implies_true,
    IsEmpty.forall_iff]
  | left::_, func _ => simp only [valid, Bool.false_eq_true, IsEmpty.forall_iff]
  | right::_, func _ => simp only [valid, Bool.false_eq_true, reduceCtorEq, imp_self, implies_true,
    IsEmpty.forall_iff]

-- A subtitution at an orthogonal position does not change validity
lemma Position.valid_substAt_of_ortho_left {p q : Position} (h₁ : p.valid t) (h₂ : q.valid t) (orth : p ⊥ q) :
  p.valid (t.substAt q h₂ u) := by
  revert h₁ h₂ orth
  match p, q, t with
  | [], _, _ => grind only [not_isOrtho_nil_left]
  | _, [], _ => grind only [not_isOrtho_nil_right]
  | m::p', n::q', t₁ @@ t₂ =>
    cases m <;> cases n
    . simp only [valid, isOrtho_cons_iff, substAt]; apply Position.valid_substAt_of_ortho_left
    . simp only [valid, substAt]; grind only
    . simp only [valid, substAt]; grind only
    . simp only [valid, isOrtho_cons_iff, substAt]; apply Position.valid_substAt_of_ortho_left
  | _::_, _::_, var _ => grind only [eq_head_of_valid_var]
  | _::_, _::_, func _ => grind only [eq_head_of_valid_func]

lemma Position.valid_substAt_of_ortho_right {p q : Position} (h₁ : p.valid t) (h₂ : q.valid t) (orth : p ⊥ q) :
  q.valid (t.substAt p h₁ u) := by
  revert h₁ h₂ orth
  match p, q, t with
  | [], _, _ => grind only [not_isOrtho_nil_left]
  | _, [], _ => grind only [not_isOrtho_nil_right]
  | m::p', n::q', t₁ @@ t₂ =>
    cases m <;> cases n
    . simp only [valid, isOrtho_cons_iff, substAt]; apply Position.valid_substAt_of_ortho_right
    . simp only [valid, substAt]; grind only
    . simp only [valid, substAt]; grind only
    . simp only [valid, isOrtho_cons_iff, substAt]; apply Position.valid_substAt_of_ortho_right
  | _::_, _::_, var _ => grind only [eq_head_of_valid_var]
  | _::_, _::_, func _ => grind only [eq_head_of_valid_func]

lemma Position.get_substAt_of_ortho_aux {p q : Position}
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (orth : p ⊥ q)
  (h₂' : q.valid (t.substAt p h₁ u))
 : q.get (t.substAt p h₁ u) h₂' = q.get t h₂ := by
  revert h₁ h₂ orth h₂'
  match p, q, t with
  | [], _, _ => simp only [IsOrtho, Bool.false_eq_true, IsEmpty.forall_iff, implies_true]
  | _, [], _ => simp only [IsOrtho, Bool.false_eq_true, IsEmpty.forall_iff, implies_true]
  | left::_, right::_, _ @@ _ =>
    simp only [substAt, get, implies_true]
  | right::_, left::_, _ @@ _ =>
    simp only [substAt, get, implies_true]
  | left::_, left::_, _ @@ _ =>
    simp only [IsOrtho, substAt, get]
    intros; apply Position.get_substAt_of_ortho_aux; grind only
  | right::_, right::_, _ @@ _ =>
    simp only [IsOrtho, substAt, get]
    intros; apply Position.get_substAt_of_ortho_aux; grind only
  | _::_, _::_, var _ => simp only [valid, Bool.false_eq_true, IsEmpty.forall_iff]
  | _::_, _::_, func _ => simp only [valid, Bool.false_eq_true, IsEmpty.forall_iff]


lemma Position.get_substAt_of_ortho {p q : Position}
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (orth : p ⊥ q)
  : q.get (t.substAt p h₁ u) (Position.valid_substAt_of_ortho_right h₁ h₂ orth) = q.get t h₂ := by
  grind only [get_substAt_of_ortho_aux]

lemma Term.substAt_comm_of_ortho_aux
  {p q : Position}
  (t u₁ u₂ : Term)
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (h₁' : p.valid (t.substAt q h₂ u₂))
  (h₂' : q.valid (t.substAt p h₁ u₁))
  (orth : p ⊥ q)
  : (t.substAt p h₁ u₁).substAt q h₂' u₂ =
    (t.substAt q h₂ u₂).substAt p h₁' u₁ := by
  revert h₁ h₂ orth
  match p, q, t with
  | [], _, _ => grind only [not_isOrtho_nil_left]
  | _, [], _ => grind only [not_isOrtho_nil_right]
  | m::p', n::q', t₁ @@ t₂ =>
    cases m <;> cases n
    . simp only [valid, substAt, isOrtho_cons_iff, app.injEq, and_true]; intros; apply Term.substAt_comm_of_ortho_aux; trivial
    . simp only [valid, substAt, implies_true]
    . simp only [valid, substAt, implies_true]
    . simp only [valid, substAt, isOrtho_cons_iff, app.injEq, true_and]; intros; apply Term.substAt_comm_of_ortho_aux; trivial
  | _::_, _::_, var _ => grind only [eq_head_of_valid_var]
  | _::_, _::_, func _ => grind only [eq_head_of_valid_func]

lemma Term.substAt_comm_of_ortho
  {p q : Position}
  (t u₁ u₂ : Term)
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (orth : p ⊥ q)
  : (t.substAt p h₁ u₁).substAt q (Position.valid_substAt_of_ortho_right h₁ h₂ orth) u₂ =
    (t.substAt q h₂ u₂).substAt p (Position.valid_substAt_of_ortho_left h₁ h₂ orth) u₁ := by
  grind only [substAt_comm_of_ortho_aux]

-- rewriting at orthogonal positions commutes
-- FIXME: rename this
lemma Rule.rewriteAt_comm_of_ortho
  {ru₁ ru₂ : Rule}
  {p q : Position}
  (t : RTerm ℛ)
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (orth : p ⊥ q)
  : ru₂.rewriteAt (ru₁.rewriteAt t p σ h₁) q τ (Position.valid_substAt_of_ortho_right h₁ h₂ orth) =
    ru₁.rewriteAt (ru₂.rewriteAt t q τ h₂) p σ (Position.valid_substAt_of_ortho_left h₁ h₂ orth) := by
  grind only [rewriteAt, substAt_comm_of_ortho]

-- Basically, if `rw₁` happens at the root, and `rw₂` happens
-- beneath a leaf of the lhs, then
-- the rewrites weakly commute.
-- To be able to prove this, I need some facts about the variable positions and how
-- they change from lhs to rhs.

-- Idea: get all the positions of a given variable `x`, show that all of them are orthogonal,
-- and show that `varSubst x t` is equal to substituting all of them 1 after another.

private abbrev Position.join (ps₁ ps₂ : List Position) : List Position :=
  (ps₁.map (left :: ·)) ++ (ps₂.map (right :: ·))

def varPos (t : Term) (x : Var) : List Position :=
  match t with
  | var y => if y = x then [[]] else [] -- bit confusing
  | func _ => []
  | t₁ @@ t₂ => Position.join (varPos t₁ x) (varPos t₂ x)

@[grind .]
lemma Position.valid_of_mem_varPos : ∀ p ∈ varPos t x, p.valid t := by
  induction t <;> simp [varPos, valid]
  case _ t₁ t₂ ih₁ ih₂ =>
    intros p shape
    rcases shape with ⟨a, h₁, h₂⟩ | ⟨a, h₁, h₂⟩
    . rw [← h₂]; simp only [valid]; grind only
    . rw [← h₂]; simp only [valid]; grind only

@[grind →]
lemma Position.get_eq_var_of_mem_varPos_aux
  (p : Position)
  (mem : p ∈ varPos t x)
  (h : p.valid t)
  : p.get t h = var x := by
  revert mem h p
  induction t
  case _ =>
    simp only [varPos, valid, List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil, or_false,
      and_imp, forall_eq_apply_imp_iff, forall_true_left, get, var.injEq]
    grind only
  case _ =>
    simp only [varPos, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  case _ t₁ t₂ ih₁ ih₂ =>
    simp only [varPos, List.mem_append, List.mem_map]
    intros p shape
    rcases shape with ⟨a, h₁, h₂⟩ | ⟨a, h₁, h₂⟩
    . rw [← h₂]; simp only [valid, get]; grind only
    . rw [← h₂]; simp only [valid, get]; grind only

lemma Position.get_eq_var_of_mem_varPos {p : Position} (mem : p ∈ varPos t x)
  : p.get t (Position.valid_of_mem_varPos p mem) = var x := by
  grind only [→ get_eq_var_of_mem_varPos_aux]

lemma Position.mem_varPos_of_get_eq_var {p : Position} {h : p.valid t}
  (isVar : p.get t h = var x) : p ∈ varPos t x := by
  revert p
  induction t
  case _ y =>
    simp only [varPos, List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil, or_false]; intros p
    cases p  -- <;> grind [Position.get] -- internal `grind` error, term has not been internalized valid (left :: tail) (t₁✝ @@ a✝)
    . simp only [get, var.injEq, and_true, imp_self, implies_true]
    . simp only [valid, Bool.false_eq_true, reduceCtorEq, and_false, imp_false, IsEmpty.forall_iff]
  case _ => intros p; cases p <;> simp only [get, reduceCtorEq, IsEmpty.forall_iff, implies_true]
  case _ =>
    intros p; cases p; simp only [get, reduceCtorEq, IsEmpty.forall_iff, implies_true]
    case _ hd tail =>
      cases hd <;> simp only [get, varPos, List.mem_append, List.cons_injective,
        List.mem_map_of_injective, List.mem_map, List.cons.injEq, reduceCtorEq, false_and,
        and_false, exists_const, or_false] <;> grind only

-- Sheesh this is awkward
lemma Position.ortho_leaf
  (h₁ : p.valid t) (h₂ : q.valid t)
  (isVar₁ : p.get t h₁ |>.isVar)
  (isVar₂ : q.get t h₂ |>.isVar)
  (neq : p ≠ q) : p ⊥ q := by
  match p, q, t with
  | left::_, right::_, t₁ @@ t₂ => grind only [= isOrtho_cons_of_ne]
  | right::_, left::_, t₁ @@ t₂ => grind only [= isOrtho_cons_of_ne]
  | right::_, right::_, t₁ @@ t₂ =>
    simp only [isOrtho_cons_iff]; simp only [get] at isVar₁; simp only [get] at isVar₂; simp only [ne_eq,
      List.cons.injEq, true_and] at neq
    apply Position.ortho_leaf (t:=t₂) <;> trivial
  | left::_, left::_, t₁ @@ t₂ =>
    simp only [isOrtho_cons_iff]; simp only [get] at isVar₁; simp only [get] at isVar₂; simp only [ne_eq,
      List.cons.injEq, true_and] at neq
    apply Position.ortho_leaf (t:=t₁) <;> trivial
  | [], [], _ => grind only
  | _::_, [], t₁ @@ t₂ => simp only [isVar, get, Bool.false_eq_true] at isVar₂
  | [], _::_, t₁ @@ t₂ => simp only [isVar, get, Bool.false_eq_true] at isVar₁
  | [], _ :: _, var _ => simp only [valid, Bool.false_eq_true] at h₂

lemma Position.ortho_varPos : ∀ p ∈ varPos t x, ∀ q ∈ varPos t x, p ≠ q → p ⊥ q := by
  intros p mem₁ q mem₂ neq; apply Position.ortho_leaf <;> try trivial
  . rw [Position.get_eq_var_of_mem_varPos_aux]
    . simp only [isVar]
    . trivial
    . grind only [valid_of_mem_varPos]
  . rw [Position.get_eq_var_of_mem_varPos_aux]
    . simp only [isVar]
    . trivial
    . grind only [valid_of_mem_varPos]

-- We used to need this now it's just for free...
lemma varPos_nodup : (varPos t x).Nodup := by
  cases t <;> simp only [varPos, List.nodup_nil]
  . grind
  . rw [List.nodup_append]
    constructor
    . rw [List.nodup_map_iff (f := fun l => left::l)]
      . apply varPos_nodup
      . simp only [List.cons_injective]
    . constructor
      . rw [List.nodup_map_iff (f := fun l => right::l)]
        . apply varPos_nodup
        . simp only [List.cons_injective]
      . simp only [List.mem_map,
         ne_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
         List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true,
         implies_true] -- holy crap

lemma Term.substAt_valid_list {p : Position} {ps : List Position}
  (h : p.valid t)
  (h' : ∀ q ∈ ps, q.valid t)
  (orth : ∀ q ∈ ps, p ≠ q → p ⊥ q)
  (mem : q ∈ ps)
  : q.valid (t.substAt p h u) := by
  by_cases eq:(q = p); simp only [eq, substAt_valid]
  grind only [valid_substAt_of_ortho_right]

def Term.substAll (t u : Term) (ps : List Position)
  (h : ∀ p ∈ ps, p.valid t)
  (orth : ∀ p ∈ ps, ∀ q ∈ ps, p ≠ q → p ⊥ q)
  : Term :=
  match ps with
  | [] => t
  | p::ps' =>
    Term.substAll
      (t.substAt p (by grind) u)
      u ps'
      (by grind [Term.substAt_valid_list])
      (by grind)

private lemma substAllMapRight
  : (t₁ @@ t₂).substAll u (List.map (fun x => right :: x) ps) h' orth' =
    (t₁ @@ t₂.substAll u ps h orth) := by
  revert t₂
  induction ps <;> intros
  . simp; eq_refl -- proof irrelevance saves the day
  case _ ih _ _ _ =>
    simp only [List.map_cons, substAll, substAt]
    apply ih

private lemma substAllAppDecomp {ps₁ ps₂ : List Position}
  (h₁ : ∀ p ∈ ps₁, p.valid t₁)
  (h₂ : ∀ p ∈ ps₂, p.valid t₂)
  (h : ∀ p ∈ Position.join ps₁ ps₂, p.valid (t₁ @@ t₂)) -- provable
  (orth₁ : ∀ p ∈ ps₁, ∀ q ∈ ps₁, p ≠ q → p ⊥ q)
  (orth₂ : ∀ p ∈ ps₂, ∀ q ∈ ps₂, p ≠ q → p ⊥ q)
  (orth : ∀ p ∈ (Position.join ps₁ ps₂), ∀ q ∈ Position.join ps₁ ps₂, p ≠ q → p ⊥ q) -- provable
  : (t₁ @@ t₂).substAll u (join ps₁ ps₂) h orth =
    ((t₁.substAll u ps₁ h₁ orth₁) @@ (t₂.substAll u ps₂ h₂ orth₂)) := by
  revert t₁
  induction ps₁ <;> intros
  . simp only [join, List.map_nil, List.nil_append, substAll]
    apply substAllMapRight
  case _ ih _ _ _ =>
    simp only [join, List.map_cons, List.cons_append, substAll, substAt]
    apply ih -- again, proof irrelevance

theorem Term.substAll_eq_varSubst (t u : Term) (x : Var) :
  t.substAll u (varPos t x) Position.valid_of_mem_varPos Position.ortho_varPos =
  t.apply (varSubst x u) := by
  induction t
  case _ y =>
    simp only [varPos, apply, varSubst]
    by_cases h:(y = x) <;> simp only [h, ↓reduceIte, substAll, substAt]
  case _ => simp only [varPos, substAll, apply]
  case _ ih₁ ih₂ =>
    simp only [varPos, apply]
    rw [substAllAppDecomp] <;> grind only -- now we pay the piper for all those hyps

-- Since orthogonal substs commute, inserting a subst into the list is the same as doing it first

-- let's first prove that rewriting at a variable reduces to rewriting at all positions of that var,
-- in 2 steps: first that rewriting at the position, then the rest of the list, is the
-- same as rewriting all at once. Then prove that a rewrite at any position is the same as
-- rewriting at some element of the `varPos` list.

lemma Term.substAt_idem {t : Term}
  (h : p.valid t)
  (h' : p.valid (t.substAt p h u)) -- this can be proven
  : (t.substAt p h u).substAt p h' u = t.substAt p h u := by
  match p, t with
  | [], _ => simp only [substAt]
  | left::_, _@@_ => simp only [substAt, app.injEq, and_true]; apply Term.substAt_idem
  | right::_, _@@_ => simp only [substAt, app.injEq, true_and]; apply Term.substAt_idem

lemma Rule.rewriteAt_is_reduce {t : RTerm ℛ}
  {mem : ru ∈ ℛ}
  (h : p.valid t)
  (mtch : ru.matchesAt t p σ h)
  : t ~> ru.rewriteAt t p σ h := by
  revert mtch
  match p, t with
  | [], _ =>
    simp only [matchesAt, matchesHead, Position.get, rewriteAt, rewriteHead, substAt]
    intros h; simp [← h]
    apply Reduces.head; trivial
  | left::p', t₁ @@ _ =>
    simp only [matchesAt, matchesHead, Position.get, rewriteAt, substAt, rewriteHead]
    intro mtch; apply Reduces.congrLeft
    apply Rule.rewriteAt_is_reduce <;> trivial
  | right::p', _ @@ t₂ =>
    simp only [matchesAt, matchesHead, Position.get, rewriteAt, substAt, rewriteHead]
    intro mtch; apply Reduces.congrRight
    apply Rule.rewriteAt_is_reduce <;> trivial

@[simp]
def RTerm.substAt (t : RTerm ℛ) (p : Position) (h : p.valid t) (u : Term) : RTerm ℛ :=
  Term.substAt t p h u

@[simp]
lemma Term.get_substAt_of_valid : substAt t p h (p.get t h') = t := by
  revert h h'
  match p, t with
  | [], _ => simp only [valid, Position.get, substAt, imp_self]
  | left::_ , _@@_ => simp only [valid, substAt, Position.get, app.injEq, and_true]; apply Term.get_substAt_of_valid
  | right::_ , _@@_ => simp only [valid, substAt, Position.get, app.injEq, true_and]; apply Term.get_substAt_of_valid
  | _::_, var _ => simp only [valid, Bool.false_eq_true, IsEmpty.forall_iff]
  | _::_, func _ => simp only [valid, Bool.false_eq_true, IsEmpty.forall_iff]

lemma Term.get_substAt : substAt t p h (p.get t h) = t := by simp

lemma Rule.rewriteAt_substAt
  {t u₁ u₂ : RTerm ℛ}
  {p : Position}
  (h : p.valid t)
  (red : u₁ ~> u₂)
  : t.substAt p h u₁ ~> t.substAt p h u₂ := by
  revert h
  match p, t with
  | [], _ =>
    simp only [RTerm.substAt, substAt]; grind only
  | left::p', t₁ @@ _ =>
    simp only [valid, RTerm.substAt, substAt]; intros
    apply Reduces.congrLeft; apply Rule.rewriteAt_substAt; grind only
  | right::p', _ @@ t₂ =>
    simp only [valid, RTerm.substAt, substAt]; intros
    apply Reduces.congrRight; apply Rule.rewriteAt_substAt; grind only
  | _::_, var _ => simp only [valid, Bool.false_eq_true, RTerm.substAt,
    IsEmpty.forall_iff]
  | _::_, func _ => simp only [valid, Bool.false_eq_true, RTerm.substAt,
    IsEmpty.forall_iff]

lemma Rule.rewriteAt_substAt_aux
  {t u₁ u₂ : RTerm ℛ}
  {p : Position}
  (h : p.valid t)
  (getAt : p.get t h = u₁)
  (red : u₁ ~> u₂)
  : t ~> t.substAt p h u₂ := by
    have h' := Term.get_substAt (h:=h)
    have h'' := Rule.rewriteAt_substAt h red
    rw [getAt] at h'
    rw [RTerm.substAt, h'] at h''
    trivial

-- A no-op substitution is a rewrite
lemma Rule.rewriteAt_is_reduce_aux {t : RTerm ℛ}
  {_ : ru ∈ ℛ}
  (h : p.valid t)
  (idem : p.get t h = ru.rhs.apply σ)
  : t ~>* ru.rewriteAt t p σ h := by
  have eq : t = ru.rewriteAt t p σ h := by
    simp only [rewriteAt, rewriteHead, ← idem, Term.get_substAt_of_valid]
  rw [← eq]
  apply refl_trans_clos.refl

lemma Term.substAll_swap {t : Term}
  (orth : p ⊥ q)
  (allValid₁ : ∀ p' ∈ p::q::ps, p'.valid t)
  (allOrth₁ : ∀ p' ∈ p::q::ps, ∀ p'' ∈ p::q::ps, p' ≠ p'' → p' ⊥ p'')
  (allValid₂ : ∀ p' ∈ q::p::ps, p'.valid t)
  (allOrth₂ : ∀ p' ∈ q::p::ps, ∀ p'' ∈ q::p::ps, p' ≠ p'' → p' ⊥ p'')
  : t.substAll u (p::q::ps) allValid₁ allOrth₁ =
    t.substAll u (q::p::ps) allValid₂ allOrth₂ := by
  simp only [substAll]
  congr 1
  apply Term.substAt_comm_of_ortho_aux; grind only

lemma Term.substAll_idem {t : Term}
  (h₁ : ∀ p' ∈ ps, p'.valid t)
  (h₂ : ∀ p' ∈ p::ps, p'.valid t)
  (orth₁ : ∀ p' ∈ ps, ∀ p'' ∈ ps, p' ≠ p'' → p' ⊥ p'')
  (orth₂ : ∀ p' ∈ p::ps, ∀ p'' ∈ p::ps, p' ≠ p'' → p' ⊥ p'')
  (mem : p ∈ ps)
  : t.substAll u (p::ps) h₂ orth₂ = t.substAll u ps h₁ orth₁ := by
  revert t
  induction ps
  case _ => simp only [List.not_mem_nil] at mem
  case _ hd tail ih =>
    by_cases h:(p = hd)
    . simp only [List.mem_cons, forall_eq_or_imp, h, or_self_left, substAll, substAt_idem,
      implies_true]
    . intros
      have h' : p ⊥ hd := by grind only [= List.mem_cons]
      rw [Term.substAll_swap] <;> try grind
      . simp [substAll]
        apply ih <;> try grind
        . simp; constructor
          . apply Position.valid_substAt_of_ortho_left <;> grind only
          . grind only [substAt_valid_list, = List.mem_cons]

lemma Rule.rewriteAt_substAll_stutter {ℛ : Rules} {t u₁ u₂ : RTerm ℛ}
  (allValid : ∀ p ∈ ps, p.valid t)
  (mtch : ∀ p (mem : p ∈ ps),
    p.get t (allValid p mem) = u₁ ∨ p.get t (allValid p mem) = u₂)
  (red : u₁ ~> u₂)
  (allOrth : ∀ p ∈ ps, ∀ q ∈ ps, p ≠ q → (p ⊥ q))
  : t ~>* t.substAll u₂ ps allValid allOrth := by
  revert t
  induction ps
  . simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, refl_trans_clos_red, substAll,
    refl_trans_clos.refl]
  case _ p ps ih =>
    intros t _ mtch
    simp only [refl_trans_clos_red, substAll]
    cases mtch p (by grind)
    case _ hl =>
      apply refl_trans_clos.step
       (b := t.substAt p (by grind) u₂)
      . apply Rule.rewriteAt_substAt_aux; trivial; grind only
      . apply ih
        intros q mem
        by_cases eq:(p = q)
        . simp [eq]
        . have pq_orth : p ⊥ q := by grind
          simp only [RTerm.substAt]
          rw [Position.get_substAt_of_ortho] <;> try grind
    case _ getEq =>
      rewrite (occs := .pos [1]) [← Term.get_substAt (t:=t) (p:=p)]
      rw [getEq]
      apply ih
      . intros q mem
        by_cases eq:(p = q)
        . simp only [eq, Position.get_substAt_of_valid, or_true]
        . have pq_orth : p ⊥ q := by grind only [= List.mem_cons]
          rw [Position.get_substAt_of_ortho] <;> try grind
      . grind only

lemma Rule.rewriteAt_substAll {ℛ : Rules}
  {t u₁ u₂ : RTerm ℛ}
  {p : Position}
  (mem' : p ∈ ps)
  (allValid : ∀ p ∈ ps, p.valid t)
  (mtch : ∀ p' (mem : p' ∈ ps), p'.get t (allValid p' mem) = u₁)
  (allOrth : ∀ p ∈ ps, ∀ q ∈ ps, p ≠ q → (p ⊥ q))
  (red : u₁ ~> u₂)
  : t.substAt p (allValid p mem') u₂ ~>*
  t.substAll u₂ ps allValid allOrth := by
  rw [← Term.substAll_idem (p := p) ] <;> try grind
  simp only [refl_trans_clos_red, RTerm.substAt, substAll]
  apply Rule.rewriteAt_substAll_stutter
  . intros q mem
    by_cases eq:(p = q)
    . simp only [eq, Position.get_substAt_of_valid, or_true]
    . have pq_orth : p ⊥ q := by grind
      rw [Position.get_substAt_of_ortho] <;> try grind
      . left; apply mtch; trivial
  . trivial

def Subst.replace (σ : Subst) (x : Var) (u : Term) : Subst :=
  fun y => if y = x then u else σ y

lemma Term.substAll_eq_substAt (t u : Term) (x : Var) :
  (t.apply τ).substAll u (varPos t x) (by grind [Position.valid_of_mem_varPos, Position.valid_apply]) Position.ortho_varPos =
  t.apply (τ.replace x u) := by
  induction t
  case _ y =>
    simp only [apply, varPos]
    by_cases h:(y = x) <;> simp [h, substAll, substAt, Subst.replace]
  case _ => simp only [apply, varPos, substAll]
  case _ ih₁ ih₂ =>
    simp only [apply, varPos]
    rw [substAllAppDecomp] -- now we pay the piper for all those hyps
    . congr
    . intros; grind only
    . intros; grind only
    . apply Position.ortho_varPos
    . apply Position.ortho_varPos

lemma Position.get_apply {p : Position}
  (h : p.valid t)
  (h' : p.valid (t.apply σ))
  : p.get (t.apply σ) h' = (p.get t h).apply σ := by
  match p, t with
  | [], _ => simp only [get]
  | left::_, t₁ @@ _ => simp only [apply, get]; apply Position.get_apply
  | right::_, _ @@ t₂ => simp only [apply, get]; apply Position.get_apply
  | _::_, var _ => simp only [valid, Bool.false_eq_true] at h
  | _::_, func _ => simp only [valid, Bool.false_eq_true] at h

lemma Rule.rewriteAt_var_eq_subst
  {ℛ : Rules}
  {t u₁ u₂ : RTerm ℛ}
  {p : Position}
  (h : p.valid t)
  (h' : p.get t h = var x)
  (mtch : τ x = u₁)
  (rew : u₁ ~> u₂)
  : (t.apply τ).substAt p (Position.valid_apply τ h) u₂ ~>*
    t.apply (τ.replace x u₂) := by
  simp only [refl_trans_clos_red, RTerm.substAt, RTerm.apply]
  rw [← Term.substAll_eq_substAt t u₂ x (τ := τ)]
  -- Notations smotations
  have h₂ := Rule.rewriteAt_substAll
   (t := t.apply τ) (u₁ := u₁) (u₂ := u₂) (p := p) (ps := varPos t x)
  simp only [RTerm.apply, ne_eq, refl_trans_clos_red, RTerm.substAt] at h₂
  apply h₂
  . apply Position.mem_varPos_of_get_eq_var <;> grind only
  . intros; rw [Position.get_apply]
    . rw [Position.get_eq_var_of_mem_varPos_aux] <;> trivial
    . grind only [valid_of_mem_varPos]
  . trivial
  . grind only [valid_apply, valid_of_mem_varPos]

structure PreCriticalPair (ℛ : Rules) where
  r₁ : Rule
  r₂ : Rule
  mem₁ : r₁ ∈ ℛ
  mem₂ : r₂ ∈ ℛ
  σ₁ : Subst
  σ₂ : Subst
  p : Position
  valid_p : p.valid r₁.lhs
  nvar_p : ¬ (p.get r₁.lhs valid_p |>.isVar)
  mtch₂ : r₂.matchesAt (r₁.lhs.apply σ₁) p σ₂ (Position.valid_apply σ₁ valid_p)

def PreCriticalPair.joins {ℛ : Rules} (cp : PreCriticalPair ℛ) : Prop :=
  let lhs : RTerm ℛ := cp.r₁.rhs.apply cp.σ₁
  let rhs : RTerm ℛ := cp.r₁.lhs.apply cp.σ₁
                         |>.substAt cp.p
                          (Position.valid_apply cp.σ₁ cp.valid_p)
                          (cp.r₂.rhs.apply cp.σ₂)
  lhs ~>*.*<~ rhs

lemma joinable_of_ortho (t : RTerm ℛ)
  (ru₁ ru₂ : Rule)
  (mem₁ : ru₁ ∈ ℛ)
  (mem₂ : ru₂ ∈ ℛ)
  (p₁ p₂ : Position)
  (h₁ : p₁.valid t)
  (h₂ : p₂.valid t)
  (σ₁ σ₂ : Subst)
  (mtch₁ : ru₁.matchesAt t p₁ σ₁ h₁)
  (mtch₂ : ru₂.matchesAt t p₂ σ₂ h₂)
  (orth : p₁ ⊥ p₂)
   : ru₁.rewriteAt t p₁ σ₁ h₁ ~>*.*<~ ru₂.rewriteAt t p₂ σ₂ h₂ := by
  exists ru₂.rewriteAt (ru₁.rewriteAt t p₁ σ₁ h₁) p₂ σ₂ (Position.valid_substAt_of_ortho_right h₁ h₂ orth)
  apply And.intro
  . apply refl_trans_clos.step _ _ _ _ (by apply refl_trans_clos.refl)
    apply Rule.rewriteAt_is_reduce; trivial
    simp only [Rule.matchesAt, Rule.matchesHead, Rule.rewriteAt, Rule.rewriteHead]
    rw [Position.get_substAt_of_ortho_aux]
    . apply mtch₂
    . trivial
    . trivial
  . apply refl_trans_clos.step _ _ _ _ (by apply refl_trans_clos.refl)
    rw [Rule.rewriteAt_comm_of_ortho] <;> try trivial
    apply Rule.rewriteAt_is_reduce; trivial
    simp only [Rule.matchesAt, Rule.matchesHead, Rule.rewriteAt, Rule.rewriteHead]
    rw [Position.get_substAt_of_ortho_aux]
    . apply mtch₁
    . trivial
    . apply Position.isOrtho_comm; trivial

lemma Rule.matchesAt_head_iff {t : Term} {ru : Rule}
  (h : ru.matchesAt t [] σ (Eq.refl true))
  : t = ru.lhs.apply σ := by
  revert h
  simp only [matchesAt, matchesHead, Position.get]
  grind only

lemma Position.valid_append {p₁ p₂ : Position}
  (h : (p₁ ++ p₂).valid t)
  : p₁.valid t := by
  revert h
  match p₁, t with
  | [], _ => simp only [valid, List.nil_append, implies_true]
  | left::_, _ @@ _ => simp only [List.cons_append, valid]; apply Position.valid_append
  | right::_, _ @@ _ => simp only [List.cons_append, valid]; apply Position.valid_append
  | _::_, var _ => simp only [List.cons_append, valid, Bool.false_eq_true, imp_self]
  | _::_, func _ => simp only [List.cons_append, valid, Bool.false_eq_true, imp_self]

lemma Position.valid_appendGet {p₁ p₂ : Position}
  (h₁ : (p₁ ++ p₂).valid t)
  (h₂ : p₁.valid t)
  : p₂.valid (p₁.get t h₂) := by
  revert h₁ h₂
  match p₁, t with
  | [], _ => simp only [valid, List.nil_append, get, forall_const, imp_self]
  | left::_, _ @@ _ => simp only [List.cons_append, valid]; apply Position.valid_appendGet
  | right::_, _ @@ _ => simp only [List.cons_append, valid]; apply Position.valid_appendGet
  | _::_, var _ => simp only [List.cons_append, valid, Bool.false_eq_true, IsEmpty.forall_iff]
  | _::_, func _ => simp only [List.cons_append, valid, Bool.false_eq_true, IsEmpty.forall_iff]

lemma Term.substAt_append {p₁ p₂ : Position}
  (h₁ : p₁.valid t)
  (h₂ : p₂.valid (p₁.get t h₁))
  (h₃ : (p₁ ++ p₂).valid t)
  : substAt t (p₁ ++ p₂) h₃ u = substAt t p₁ h₁ (substAt (p₁.get t h₁) p₂ h₂ u) := by
  revert h₁
  match p₁, t with
  | [], _ => simp [Position.get, substAt]
  | left::_, _ @@ _ => simp only [Position.get, List.cons_append, substAt, app.injEq, and_true]; intros; apply Term.substAt_append
  | right::_, _ @@ _ => simp only [Position.get, List.cons_append, substAt, app.injEq, true_and]; intros; apply Term.substAt_append
  | _::_, var _ => simp only [valid, Bool.false_eq_true, List.cons_append, IsEmpty.forall_iff]
  | _::_, func _ => simp only [valid, Bool.false_eq_true, List.cons_append, IsEmpty.forall_iff]

lemma Rule.matchesAt_append {p₁ p₂ : Position} {ru : Rule}
  (h₁ : p₁.valid t)
  (h₂ : p₂.valid (p₁.get t h₁))
  (h₃ : (p₁ ++ p₂).valid t)
  (mtchConcat : ru.matchesAt t (p₁ ++ p₂) σ h₃)
  : ru.matchesAt (p₁.get t h₁) p₂ σ h₂ := by
  revert mtchConcat
  simp only [matchesAt, matchesHead, get_append, imp_self]

lemma Rule.rewriteAt_replace {t : RTerm ℛ}
  (rewAt : let u' : RTerm ℛ := σ x; u' ~> u)
  : t.apply σ ~>* t.apply (σ.replace x u) := by
  induction t
  case _ y =>
    by_cases h:(y = x)
    . simp only [refl_trans_clos_red, RTerm.apply, apply, h, Subst.replace, ↓reduceIte]
      apply refl_trans_clos.step _ _ _ _ (by apply refl_trans_clos.refl)
      trivial
    . simp only [refl_trans_clos_red, RTerm.apply, apply, Subst.replace]
      simp only [h]
      apply refl_trans_clos.refl
  case _ => simp only [refl_trans_clos_red, RTerm.apply, apply]; apply refl_trans_clos.refl
  case _ =>
    simp only [refl_trans_clos_red, RTerm.apply, apply]
    apply Reduces.refl_trans_clos_congr <;> trivial

lemma IsNotOuterValid {p : Position}
  (h : p.valid <| t.apply σ)
  (isNOuter : ¬ IsOuterPosition p t σ)
  : p.valid t  := by
  revert h isNOuter
  match p, t with
  | [], _ => simp only [valid, Bool.not_eq_true, implies_true]
  | left::_, _ @@ _ =>
    simp only [apply, valid, IsOuterPosition, splitOnSubst, Position.get, Bool.dite_else_false,
      not_exists, Bool.not_eq_true]
    intros; apply IsNotOuterValid
    . trivial
    . simp only [IsOuterPosition, Bool.dite_else_false, not_exists, Bool.not_eq_true]; grind only
  | right::_, _ @@ _ =>
    simp only [apply, valid, IsOuterPosition, splitOnSubst, Position.get, Bool.dite_else_false,
      not_exists, Bool.not_eq_true]
    intros; apply IsNotOuterValid
    . trivial
    . simp only [IsOuterPosition, Bool.dite_else_false, not_exists, Bool.not_eq_true]; grind only
  | _::_, var _ =>
    simp [IsOuterPosition, splitOnSubst, Position.get, valid, Term.isVar]
  | _::_, func _ =>
    simp only [apply, valid, Bool.false_eq_true, Bool.not_eq_true, imp_false, Bool.not_eq_false,
      IsEmpty.forall_iff]

-- FIXME: this is a dumb proof, could just induct on `t`.
lemma IsNotOuterNvar_aux
  (h : p.valid t)
  (isNOuter : ¬ IsOuterPosition p t σ)
  : (p.get t h |>.isVar) = false := by
  revert h isNOuter
  match p, t with
  | [], _ => simp only [valid, IsOuterPosition, splitOnSubst_head, ↓reduceDIte, Bool.not_eq_true,
    imp_self]
  | left::_, _ @@ _ =>
    simp only [valid, IsOuterPosition, splitOnSubst, Position.get, Bool.dite_else_false, not_exists,
      Bool.not_eq_true]
    intros; apply IsNotOuterNvar_aux
    . simp only [IsOuterPosition, Bool.dite_else_false, not_exists, Bool.not_eq_true]; trivial
  | right::_, _ @@ _ =>
    simp only [valid, IsOuterPosition, splitOnSubst, Position.get, Bool.dite_else_false, not_exists,
      Bool.not_eq_true]
    intros; apply IsNotOuterNvar_aux
    . simp only [IsOuterPosition, Bool.dite_else_false, not_exists, Bool.not_eq_true]; trivial
  | _::_, var _ =>
    simp only [valid, Bool.false_eq_true, Bool.not_eq_true, IsEmpty.forall_iff]
  | _::_, func _ =>
    simp only [valid, Bool.false_eq_true, Bool.not_eq_true, IsEmpty.forall_iff]

lemma IsNotOuterNvar
  (h : p.valid t)
  (isNOuter : ¬ IsOuterPosition p t σ)
  : ¬ (p.get t h |>.isVar) := by simp; apply IsNotOuterNvar_aux <;> trivial

lemma joinable_of_top (t : RTerm ℛ)
  (joinable : ∀ cp : PreCriticalPair ℛ, cp.joins)
  (ru₁ ru₂ : Rule)
  (mem₁ : ru₁ ∈ ℛ)
  (mem₂ : ru₂ ∈ ℛ)
  (p₂ : Position)
  (h₂ : p₂.valid t)
  (σ₁ σ₂ : Subst)
  (mtch₁ : ru₁.matchesAt t [] σ₁ (Eq.refl true))
  (mtch₂ : ru₂.matchesAt t p₂ σ₂ h₂)
   : ru₁.rewriteHead σ₁ ~>*.*<~ ru₂.rewriteAt t p₂ σ₂ h₂ := by
  by_cases isOuter:(IsOuterPosition p₂ ru₁.lhs σ₁)
  -- This case is awkward: though we're rewriting *at* `p₂` (with `rewriteAt`)
  -- we want to consider a rewrite at a higher position, that of a variable
  -- in `ru₁.lhs`, so we can apply `Rule.rewriteAt_var_eq_subst`.
  -- This is not a head rewrite though.
  . have ⟨p₁, ⟨p₂', ⟨x, ⟨h, ⟨h', h''⟩⟩⟩⟩⟩ := IsOuterPosition.exists_split isOuter
    revert mtch₂ isOuter h₂; rw [h']; intros h₂ mtch₂ isOuter
    simp only [Rule.rewriteHead, Rule.rewriteAt]
    have h₁₁ : p₁.valid t := by apply Position.valid_append; trivial
    have h₁₂ : p₂'.valid (p₁.get t h₁₁) := by apply Position.valid_appendGet; trivial
    rw [Term.substAt_append (t:=t) (h₁ := h₁₁) (h₂ := h₁₂)]
    let u : RTerm ℛ := (p₁.get t h₁₁).substAt p₂' h₁₂ (ru₂.rhs.apply σ₂)
    let u_l : RTerm ℛ := σ₁ x
    have h₅ : σ₁ x = p₁.get t h₁₁ := by
      calc
        σ₁ x = (var x).apply σ₁ := by simp only [apply]
        _    = (p₁.get ru₁.lhs h).apply σ₁ := by rw [← h'']
        _    = (p₁.get (ru₁.lhs.apply σ₁) (Position.valid_apply σ₁ h)) := by rw [Position.get_apply]
        _    = (p₁.get t h₁₁) := by congr
    have u_rew : u_l ~> u := by -- This is the most finicky proof I have ever done
      simp only [Rule.matchesAt, Rule.matchesHead, get_append] at mtch₂
      have h₃ : p₂'.valid u_l := by
        simp only [Rule.matchesAt, Position.get] at mtch₁
        simp only [u_l]
        have h₄ := Position.valid_append_right h₂
        rw [h₅]; trivial
      simp only [u_l, u]; rw [h₅]
      apply Rule.rewriteAt_is_reduce <;> trivial
    exists (ru₁.rhs.apply (σ₁.replace x u))
    apply And.intro
    . apply Rule.rewriteAt_replace; trivial
    . have h₆ :
       substAt t p₁ h₁₁ ((p₁.get t h₁₁).substAt p₂' h₁₂ (ru₂.rhs.apply σ₂)) =
       substAt t p₁ h₁₁ u := by trivial
      rw [h₆]
      -- Very annoying
      let u' : RTerm ℛ := ru₁.lhs.apply (σ₁.replace x u)
      apply refl_trans_clos_trans (y := u')
      simp only [Rule.matchesAt, Rule.matchesHead, Position.get] at mtch₁
      simp only [refl_trans_clos_red, ← mtch₁]; simp only [u']
      . apply Rule.rewriteAt_var_eq_subst <;> trivial
      . simp only [refl_trans_clos_red, u']
        apply refl_trans_clos.step _ _ _ _ (by apply refl_trans_clos.refl)
        simp only [Red.reduces]; apply Reduces.head
        trivial
  . simp only [PreCriticalPair.joins] at joinable
    let cp : PreCriticalPair ℛ := by
      apply PreCriticalPair.mk ru₁ ru₂ mem₁ mem₂ σ₁ σ₂ p₂
      . apply IsNotOuterNvar; trivial
      . simp only [Rule.matchesAt, Rule.matchesHead, Position.get] at mtch₁
        simp only [mtch₁]
        trivial
      . simp only [Rule.matchesAt, Rule.matchesHead, Position.get] at mtch₁
        rw [← mtch₁] at h₂
        apply IsNotOuterValid <;> trivial
    have joins := joinable cp
    simp only [cp] at joins
    simp only [Rule.rewriteHead, Rule.rewriteAt]
    simp only [Rule.matchesAt, Rule.matchesHead, Position.get] at mtch₁
    simp only [← mtch₁]
    apply joins

lemma joins_congr_left {t₁ t₂ u : RTerm ℛ}
  (joins : t₁ ~>*.*<~ t₂)
  : (t₁ @@@ u) ~>*.*<~ (t₂ @@@ u) := by
  have ⟨t', _⟩ := joins
  exists (t' @@@ u); grind only [Reduces.refl_trans_clos_congr_left]

lemma joins_congr_right {t u₁ u₂ : RTerm ℛ}
  (joins : u₁ ~>*.*<~ u₂)
  : (t @@@ u₁) ~>*.*<~ (t @@@ u₂) := by
  have ⟨u', _⟩ := joins
  exists (t @@@ u'); grind only [Reduces.refl_trans_clos_congr_right]

lemma joinable_mono (t : RTerm ℛ)
  (joinable : ∀ cp : PreCriticalPair ℛ, cp.joins)
  (ru₁ ru₂ : Rule)
  (mem₁ : ru₁ ∈ ℛ)
  (mem₂ : ru₂ ∈ ℛ)
  (p₁ p₂ : Position)
  (h₁ : p₁.valid t)
  (h₂ : p₂.valid t)
  (σ₁ σ₂ : Subst)
  (mtch₁ : ru₁.matchesAt t p₁ σ₁ h₁)
  (mtch₂ : ru₂.matchesAt t p₂ σ₂ h₂)
  (inc : p₁ ⊆ p₂)
   : ru₁.rewriteAt t p₁ σ₁ h₁ ~>*.*<~ ru₂.rewriteAt t p₂ σ₂ h₂ := by
  match p₁, p₂ with
  | [], _ =>
    have h := joinable_of_top (ru₁:=ru₁) (ru₂:=ru₂) (t:=t)
    simp only [Rule.rewriteHead] at h
    simp only [Rule.rewriteAt, Rule.rewriteHead, substAt]
    apply h <;> trivial
  | left::p₁', left::p₂' =>
    cases t
    case _ => simp only [valid, Bool.false_eq_true] at h₁
    case _ => simp only [valid, Bool.false_eq_true] at h₁
    case _ =>
      simp only [Rule.rewriteAt, substAt, Rule.rewriteHead]
      apply joins_congr_left
      apply joinable_mono <;> trivial
  | right::p₁', right::p₂' =>
    cases t
    case _ => simp only [valid, Bool.false_eq_true] at h₁
    case _ => simp only [valid, Bool.false_eq_true] at h₁
    case _ =>
      simp only [Rule.rewriteAt, substAt, Rule.rewriteHead]
      apply joins_congr_right
      apply joinable_mono <;> trivial
  | left::p₁', right::p₂' => simp only [Subset, Inc, Bool.false_eq_true] at inc
  | right::p₁', left::p₂' => simp only [Subset, Inc, Bool.false_eq_true] at inc


-- This is almost the main theorem: any failure to be locally confluent *must* come from
-- a non-joinable pre-critical pair.
-- The converse is true as well, but we only state the "if" direction
theorem PreCritJoinableWC {ℛ : Rules}
  (joinable : ∀ cp : PreCriticalPair ℛ, cp.joins)
  : weakly_confluent (termRed ℛ) := by
  simp [weakly_confluent]
  intros t u₁ u₂ red₁ red₂
  have ⟨ru₁, ⟨mem₁, ⟨p₁, ⟨σ₁,⟨h₁, ⟨mtch₁, rew₁⟩⟩⟩⟩⟩⟩ := Reduces.exists_rewriteAt _ _ red₁
  have ⟨ru₂, ⟨mem₂, ⟨p₂, ⟨σ₂,⟨h₂, ⟨mtch₂, rew₂⟩⟩⟩⟩⟩⟩ := Reduces.exists_rewriteAt _ _ red₂
  rcases Position.trichotomy p₁ p₂ with h | h | h
  . rw [rew₁, rew₂]; apply joinable_mono <;> grind only
  . rw [rew₁, rew₂]; apply joins_comm; apply joinable_mono <;> grind only
  . rw [rew₁, rew₂]; apply joinable_of_ortho <;> grind only

-- breaks abstraction of `Var`.
private def getStringPrefix (avoid : Finset Var) (h : avoid.Nonempty) : String :=
  let avoidLen : Finset ℕ := avoid.image String.length
  let max := avoidLen.max' (by simp [avoidLen]; exact h)
  List.replicate (max+1) '_' |> String.ofList

-- Magic. Needs to be injective!
def freshVar (base : Var) (avoid : Finset Var) : Var :=
  if h: avoid.Nonempty then
    let base' : String := base
    (getStringPrefix avoid h) ++ base'
  else
    base

-- Jeesh
def freshVarInv (renamed : Var) (avoid : Finset Var) : Var :=
  if h: avoid.Nonempty then
    let dropLen := getStringPrefix avoid h |>.length
    renamed |>.toList.drop dropLen |> String.ofList
  else
    renamed

lemma freshVar_not_mem
  : freshVar x S ∉ S := by
  simp [freshVar]
  by_cases h:(S.Nonempty) <;> simp only [h]
  . simp only [getStringPrefix]
    intro h'
    have h' := Finset.mem_image_of_mem String.length h'
    simp at h'
    have ⟨a, h'⟩ := h'
    have h'' : ∀ b ∈ S, b.length < (Finset.image String.length S).max' (by simp; exact h) + 1 := by
      intros b mem
      have h : (String.length b ∈ Finset.image String.length S) := by simp only [Finset.mem_image]; exists b
      have h := Finset.le_max' _ _ h
      grind only
    have h'' := h'' a h'.1
    grind only
  . simp only [Finset.not_nonempty_iff_eq_empty] at h; simp only [h, Finset.notMem_empty,
    not_false_eq_true]

lemma freshVar_inv_inv :
  freshVarInv (freshVar x S) S = x := by
  simp [freshVar, freshVarInv]
  by_cases h:S.Nonempty <;> simp only [h, ↓reduceDIte, String.toList_append, String.length_toList,
    List.drop_left', String.ofList_toList]

lemma freshVar_distinct
  (neq : x ≠ y)
  : freshVar x S ≠ freshVar y S := by
  intro h
  have h' : freshVarInv (freshVar x S) S = freshVarInv (freshVar y S) S := by grind
  grind only [!freshVar_inv_inv]

def Subst.ren (avoid : Finset Var) : Subst := fun x => var <| freshVar x avoid

def Subst.joinAvoiding (σ₁ : Subst) (σ₂ : Subst) (S : Finset Var) : Subst :=
  fun x => if x ∈ S then σ₂ x else σ₁ (freshVarInv x S)

lemma Subst.join_apply_left (σ₁ : Subst) (σ₂ : Subst)
  : (Subst.ren S).scomp (σ₁.joinAvoiding σ₂ S) = σ₁ := by
  funext x; simp only [scomp, ren, apply, joinAvoiding]
  simp only [freshVar_not_mem, ↓reduceIte, freshVar_inv_inv]

lemma Subst.join_apply_right {t : Term} {σ₁ σ₂ : Subst}
  {S : Finset Var}
  (h : t.vars ⊆ S)
  : t.apply (σ₁.joinAvoiding σ₂ S) = t.apply σ₂ := by
  revert h
  induction t
  case var x => simp only [vars, Finset.singleton_subset_iff, apply, joinAvoiding, ite_eq_left_iff]; grind only
  case func _ => simp only [apply, implies_true]
  case app h₁ h₂ => simp only [vars, apply, app.injEq]; grind only [= Finset.subset_iff,
    = Finset.mem_union]


lemma Rule.matches_unifies {t₁ t₂ : Term}
  (h : t₁.apply σ₁ = t₂.apply σ₂)
  (h' : t₂.vars ⊆ S)
  : Unifier (σ₁.joinAvoiding σ₂ S) (t₁.apply <| Subst.ren S) t₂ := by
  simp only [Unifier]
  rw [← Subst.scomp_apply]
  simp only [Subst.join_apply_left]
  rw [Subst.join_apply_right] <;> grind


lemma Rule.match_unify {t₁ t₂ : Term}
  (h : t₁.apply σ₁ = t₂.apply σ₂)
  (_ : t₂.vars ⊆ S)
  : Unify (t₁.apply <| Subst.ren S) t₂ := by
  exists σ₁.joinAvoiding σ₂ S
  apply Rule.matches_unifies <;> trivial

structure CriticalPair (ℛ : Rules) where
  ru₁ : Rule
  ru₂ : Rule
  mem₁ : ru₁ ∈ ℛ
  mem₂ : ru₂ ∈ ℛ
  p : Position
  valid_p : p.valid ru₁.lhs
  unifies : unify
   (p.get ru₁.lhs valid_p |>.apply (Subst.ren (ru₂.lhs.vars ∪ ru₂.rhs.vars)))
   ru₂.lhs
   |>.isSome

def CriticalPair.joins (cp : CriticalPair ℛ) : Prop :=
  let avoids := cp.ru₂.lhs.vars ∪ cp.ru₂.rhs.vars
  let renMatch := cp.p.get cp.ru₁.lhs cp.valid_p
                 |>.apply (Subst.ren avoids)
  let mgu := unify renMatch cp.ru₂.lhs |>.get cp.unifies
  let lhs : RTerm ℛ := cp.ru₁.rhs.apply (Subst.ren avoids) |>.apply mgu
  let rhs : RTerm ℛ :=
    (cp.ru₁.lhs.apply (Subst.ren avoids) |>.apply mgu).substAt cp.p
    (Position.valid_apply mgu (Position.valid_apply (Subst.ren avoids) cp.valid_p))
    (cp.ru₂.rhs.apply mgu)
  lhs ~>*.*<~ rhs

lemma UnifySymm  (h : Unify t u) : Unify u t := by
  rcases h with ⟨σ, _⟩
  exists σ; apply Unifier.symm; trivial

lemma unif_crit_isSome
  (cp : PreCriticalPair ℛ)
  : (unify ((cp.p.get cp.r₁.lhs cp.valid_p).apply (Subst.ren <| cp.r₂.lhs.vars ∪ cp.r₂.rhs.vars))
            cp.r₂.lhs).isSome := by
  apply unify_progress
  apply Rule.matches_unifies
  . have h := cp.mtch₂
    simp only [Rule.matchesAt, Rule.matchesHead] at h
    rw [← Position.get_apply, h]
  . simp only [Finset.subset_union_left]

def critical_of_preCritical (cp : PreCriticalPair ℛ) : CriticalPair ℛ :=
  CriticalPair.mk
    cp.r₁
    cp.r₂
    cp.mem₁
    cp.mem₂
    cp.p
    cp.valid_p
    (unif_crit_isSome cp)

-- ugh
lemma rewrite_apply_subst
  {t u : Term}
  {σ σ' : Subst}
  {p : Position}
  (h₁ : p.valid t)
  (h₃ : σ' = σ)
  (h₂ : p.valid (t.apply σ))
  : (t.apply σ).substAt p h₂ u = (t.apply σ').substAt p (Position.valid_apply σ' h₁) u := by
  symm at h₃
  congr

-- can't believe I haven't needed this
lemma Term.apply_substAt {t u : Term}
  (h : p.valid t)
  (h' : p.valid (t.apply σ))
  : (t.substAt p h u).apply σ = (t.apply σ).substAt p h' (u.apply σ) := by
  revert h h'
  match p, t with
  | [], _ => simp only [substAt, implies_true]
  | left::_, _ @@ _ => simp only [valid, apply, substAt, app.injEq, and_true]; apply Term.apply_substAt
  | right::_, _ @@ _ => simp only [valid, apply, substAt, app.injEq, true_and]; apply Term.apply_substAt
  | _::_, var _ => simp only [valid, Bool.false_eq_true, IsEmpty.forall_iff]
  | _::_, func _ => simp only [valid, Bool.false_eq_true, IsEmpty.forall_iff]

lemma joins_apply {t u : RTerm ℛ}
  (joins_t_u : t ~>*.*<~ u)
  : t.apply σ ~>*.*<~ u.apply σ := by
  have ⟨v, _⟩ := joins_t_u
  simp only [joins, refl_trans_clos_red, RTerm.apply]; exists (v.apply σ)
  apply And.intro <;> apply Reduces.refl_trans_clos_apply <;> grind only

lemma JoinsCPImpJoinsPC
  (cp : PreCriticalPair ℛ)
  (joins : (critical_of_preCritical cp).joins)
  : cp.joins := by
  cases cp
  case _ r₁ r₂ mem₁ mem₂ σ₁ σ₂ p valid_p nvar mtch =>
  simp only [CriticalPair.joins, critical_of_preCritical] at joins
  simp only [PreCriticalPair.joins]
  simp only [Rule.matchesAt, Rule.matchesHead] at mtch
  have h := Rule.matches_unifies (σ₁:=σ₁) (σ₂:=σ₂) (t₁ := p.get r₁.lhs valid_p) (t₂ := r₂.lhs) (S := r₂.lhs.vars ∪ r₂.rhs.vars)
            (by rw [← Position.get_apply]; symm; trivial)
            (by simp)
  have ⟨τ, isUnif⟩ := unify_complete h
  rw (occs:= .pos [1]) [← Subst.join_apply_left (σ₁:=σ₁) (σ₂:=σ₂) (S := r₂.lhs.vars ∪ r₂.rhs.vars)]
  have h := Subst.join_apply_right (t:=r₂.rhs) (σ₁:=σ₁) (σ₂:=σ₂) (S := r₂.lhs.vars ∪ r₂.rhs.vars) (by simp)
  rw [← h]
  rw [
      rewrite_apply_subst valid_p
        (Subst.join_apply_left (σ₁:=σ₁) (σ₂:=σ₂) (S := r₂.lhs.vars ∪ r₂.rhs.vars))
         (u:=(r₂.rhs.apply (σ₁.joinAvoiding σ₂ (r₂.lhs.vars ∪ r₂.rhs.vars))))]
  simp only [Subst.scomp_apply]
  rw [isUnif]
  simp only [Subst.scomp_apply] -- horror!!!!
  rw [← Term.apply_substAt]
  . apply joins_apply
    trivial

-- This is the main theorem: any failure to be locally confluent *must* come from
-- a non-joinable critical pair.
-- The converse is true as well, but we only state the "if" direction
theorem critical_pair_lemma {ℛ : Rules}
  (joinable : ∀ cp : CriticalPair ℛ, cp.joins)
  : weakly_confluent (termRed ℛ) := by
  apply PreCritJoinableWC
  grind only [JoinsCPImpJoinsPC]

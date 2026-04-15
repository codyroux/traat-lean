import Traat.chapter3
import Mathlib.Data.Finset.Max

section Position

#print Option

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
  revert h; induction p <;> grind [Position.valid]

@[simp, grind .]
lemma Position.eq_head_of_valid_func (h : p.valid (func x)) : p = Position.head := by
  revert h; induction p <;> grind [Position.valid]


lemma Position.valid_apply {p : Position} {t : Term} (σ : Subst)
  (h : p.valid t)
  : p.valid <| t.apply σ := by
  match p, t with
  | [], _ => simp [valid]
  | left::ps, t₁ @@ t₂ =>
    simp [apply, valid]; apply Position.valid_apply
    . simp [valid] at h; trivial
  | right::ps, t₁ @@ t₂ =>
    simp [apply, valid]; apply Position.valid_apply
    . simp [valid] at h; trivial
  | _::_, var _ => simp [valid] at h
  | _::_, func _ => simp [valid] at h

lemma Position.valid_append_left {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : p₁.valid t := by
  revert h
  match p₁, t with
  | [], _ => simp [Position.valid]
  | left::_, t₁ @@ _ => simp [Position.valid]; intro h; apply Position.valid_append_left h
  | right::_, _ @@ t₂ => simp [Position.valid]; intro h; apply Position.valid_append_left h
  | _::_, var _ => simp [Position.valid]
  | _::_, func _ => simp [Position.valid]

lemma Position.valid_append_right {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : p₂.valid <| p₁.get t (Position.valid_append_left h) := by
  revert h
  match p₁, t with
  | [], _ => simp [Position.valid, Position.get]
  | left::_, t₁ @@ _ => simp [Position.valid, Position.get]; intro h; apply Position.valid_append_right h
  | right::_, _ @@ t₂ => simp [Position.valid, Position.get]; intro h; apply Position.valid_append_right h
  | _::_, var _ => simp [Position.valid]
  | _::_, func _ => simp [Position.valid]

@[simp]
lemma Position.get_append {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : (p₁ ++ p₂).get t h = p₂.get (p₁.get t <| Position.valid_append_left h) (Position.valid_append_right h) := by
  revert h
  match p₁, t with
  | [], _ => simp [Position.valid, Position.get]
  | left::_, t₁ @@ _ => simp [Position.valid, Position.get]; intro h; apply Position.get_append h
  | right::_, _ @@ t₂ => simp [Position.valid, Position.get]; intro h; apply Position.get_append h
  | _::_, var _ => simp [Position.valid]
  | _::_, func _ => simp [Position.valid]

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
  induction t <;> simp [Position.splitOnSubst]

lemma Position.splitOnSubst_fst_valid {p : Position} (h : p.valid (t.apply σ))
  : (p.splitOnSubst t σ).fst |>.valid t := by
  revert h
  match p, t with
  | [], _ => simp [Position.valid]
  | left::p', t₁ @@ _ =>
    simp [Position.splitOnSubst, apply, Position.valid]
    intros; apply Position.splitOnSubst_fst_valid; grind
  | right::p', _ @@ t₂ =>
    simp [Position.splitOnSubst, apply, Position.valid]
    intros; apply Position.splitOnSubst_fst_valid; grind
  | _, var _ =>
    simp [Position.valid, Position.splitOnSubst, apply]
  | _, func _ =>
    simp [Position.valid, Position.splitOnSubst, apply]

lemma Position.splitOnSubst_concat {p : Position}
 : (p.splitOnSubst t σ).1 ++ (p.splitOnSubst t σ).2 = p := by
  match p, t with
  | [], _ => simp
  | left::p', t₁ @@ _ =>
    simp [Position.splitOnSubst]
    apply Position.splitOnSubst_concat
  | right::p', _ @@ t₂ =>
    simp [Position.splitOnSubst]
    apply Position.splitOnSubst_concat
  | _, var _ =>
    simp [Position.splitOnSubst]
  | _, func _ =>
    simp [Position.splitOnSubst]

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
    simp [IsOuterPosition, Position.valid]
    intros t; cases t <;> grind [isVar, Position.get]
  case _ hd tail ih =>
    intros t
    cases t
    case var y =>
      intros _
      exists [], (hd::tail), y, (Eq.refl true)
    case func _ =>
      simp [IsOuterPosition, Position.splitOnSubst, Position.valid, Position.get, isVar]
    case app t₁ t₂ =>
      cases hd
      case _ =>
        intros h
        have h' : IsOuterPosition tail t₁ σ := by exact h
        have ⟨p₁, ⟨p₂, ⟨y, ⟨h₁, _⟩⟩⟩⟩ := ih h'
        exists (left::p₁), p₂, y, h₁
        simp [Position.get]; grind
      case _ =>
        intros h
        have h' : IsOuterPosition tail t₂ σ := by exact h
        have ⟨p₁, ⟨p₂, ⟨y, ⟨h₁, _⟩⟩⟩⟩ := ih h'
        exists (right::p₁), p₂, y, h₁
        simp [Position.get]; grind

-- define subst-at, rewrite-at, prove that you can always replace a rewrite with a rewrite at

def Term.substAt (t : Term) (p : Position) (h : p.valid t) (u : Term) : Term :=
match p, t with
| [], _ => u
| left::p', t₁ @@ t₂ => (Term.substAt t₁ p' h u) @@ t₂
| right::p', t₁ @@ t₂ => t₁ @@ (Term.substAt t₂ p' h u)
| _::_, var _ => by simp [Position.valid] at h
| _::_, func _ => by simp [Position.valid] at h

lemma Term.substAt_valid_aux {p : Position} (h : p.valid t)
  : p.valid (t.substAt p h u) := by
  revert h
  match p, t with
  | [], _ => simp [Position.valid]
  | left::p', t₁ @@ _ =>
    simp [Position.valid, substAt]
    apply Term.substAt_valid_aux
  | right::p', _ @@ t₂ =>
    simp [Position.valid, substAt]
    apply Term.substAt_valid_aux
  | _::_, var _ => simp [Position.valid, substAt]
  | _::_, func _ => simp [Position.valid, substAt]

@[simp]
lemma Position.get_substAt_of_valid {t : Term} {p : Position}
 (h : p.valid t)
 (h' : p.valid (t.substAt p h u))
 : p.get (t.substAt p h u) h' = u := by
  revert h
  match p, t with
  | [], _ => simp [Position.valid, substAt, Position.get]
  | left::p', t₁ @@ _ =>
    simp [Position.valid, substAt, substAt]
    apply Position.get_substAt_of_valid
  | right::p', _ @@ t₂ =>
    simp [Position.valid, substAt, substAt]
    apply Position.get_substAt_of_valid
  | _::_, var _ => simp [Position.valid, substAt]
  | _::_, func _ => simp [Position.valid, substAt]

lemma Position.get_substAt {t : Term} {p : Position} (h : p.valid t)
 : p.get (t.substAt p h u) (Term.substAt_valid_aux h) = u := by
 simp

def Position.Inc (p q : Position) : Bool :=
match p, q with
| [], _ => true
| left::p', left::q' => Position.Inc p' q'
| right::p', right::q' => Position.Inc p' q'
| _, _ => false

#print HasSubset

instance Position.instHasSubset : HasSubset Position where
  Subset p q := Position.Inc p q

@[simp]
lemma Position.empty_subset {p : Position} : [] ⊆ p := by
  simp [Subset, Position.Inc]

@[simp]
lemma Position.not_cons_subset_empty {p : Position} : ¬ m::p ⊆ [] := by
  simp [Subset, Position.Inc]

@[simp]
lemma Position.cons_subset_cons_iff {p q : Position} : (m::p ⊆ m::q) = (p ⊆ q) := by
  cases m
  . match p, q with
    | [], _ => simp [Subset, Position.Inc]
    | left::p', left::q' => simp [Subset, Position.Inc]
    | right::p', right::q' => simp [Subset, Position.Inc]
    | _, _ => simp [Subset, Position.Inc]
  . match p, q with
    | [], _ => simp [Subset, Position.Inc]
    | left::p', left::q' => simp [Subset, Position.Inc]
    | right::p', right::q' => simp [Subset, Position.Inc]
    | _, _ => simp [Subset, Position.Inc]

@[grind .]
lemma Position.not_cons_subset_cons_of_ne {p q : Position} (h : m ≠ n) : ¬ (m::p ⊆ n::q) := by
  revert h
  cases m <;> cases n <;> simp [Subset, Position.Inc]

-- A little tedium here
@[grind →]
lemma Position.valid_of_valid_of_subset {p q : Position} (h : q.valid t) (inc : p ⊆ q)
 : p.valid t := by
  revert inc h; simp [Subset]
  match p, q, t with
  | [], _, _ => simp [Position.valid]
  | left::p', left::q', t₁ @@ _ =>
    simp [Position.valid, Position.Inc]
    apply Position.valid_of_valid_of_subset
  | right::p', right::q', _ @@ t₂ =>
    simp [Position.valid, Position.Inc]
    apply Position.valid_of_valid_of_subset
  | _, _::_, var _ => simp [Position.valid]
  | _, _::_, func _ => simp [Position.valid]
  | _::_, [], _ => simp [Position.Inc]
  | right::_, left::_, _ => simp [Position.Inc]
  | left::_, right::_, _ => simp [Position.Inc]

#check SDiff

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
  induction p <;> simp [SDiff.sdiff, Position.sdiff]

@[simp]
lemma Position.empty_sdiff {p : Position} : [] \ p = [] := by
  induction p <;> simp [SDiff.sdiff, Position.sdiff]

@[simp]
lemma Position.sdiff_cons_cons {p q : Position} {m : Move} : (m::p) \ (m::q) = p \ q := by
  cases m <;> simp [SDiff.sdiff, Position.sdiff]

@[simp]
lemma Position.sdiff_self {p : Position} : (p \ p) = [] := by
  induction p <;> simp; trivial

lemma Position.eq_append_sdiff_of_subset {p q : Position} (inc : p ⊆ q) : q = p ++ (q \ p) := by
  revert inc
  cases p <;> cases q <;> simp
  case cons.cons m _ n _ =>
    by_cases h:(m = n)
    . simp [h]; apply Position.eq_append_sdiff_of_subset
    . grind

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
  revert h; cases m <;> cases n <;> simp [Position.IsOrtho]

@[simp]
lemma Position.isOrtho_cons_iff : ((m::p) ⊥ (m::q)) = (p ⊥ q) := by
  cases m <;> simp only [Position.IsOrtho]

@[grind .]
lemma Position.not_isOrtho_nil_left : ¬ ([] ⊥ p) := by
  cases p <;> simp [Position.IsOrtho]

@[grind .]
lemma Position.not_isOrtho_nil_right : ¬ (p ⊥ []) := by
  cases p <;> simp [Position.IsOrtho]

lemma Position.trichotomy (p q : Position) : p ⊆ q ∨ q ⊆ p ∨ p ⊥ q := by
  cases p <;> cases q <;> try simp
  case cons.cons m _ n _ =>
    by_cases h:(m = n)
    . simp [h]; apply Position.trichotomy
    . grind

lemma Position.isOrtho_comm {p q : Position} (h : p ⊥ q) : q ⊥ p := by
  revert h
  match p, q with
  | [], _ => simp [Position.IsOrtho]
  | _::_, [] => simp [Position.IsOrtho]
  | left::_, left::_ => simp [Position.IsOrtho]; apply Position.isOrtho_comm
  | right::_, right::_ => simp [Position.IsOrtho]; apply Position.isOrtho_comm
  | left::_, right::_ => simp [Position.IsOrtho]
  | right::_, left::_ => simp [Position.IsOrtho]

end Position

open Position Move Term

#print Reduces
#print Rules
#print Rule

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
    simp [Rule.rewriteAt, Term.substAt, Rule.matchesAt, Position.get]
  case _ ih =>
    let ⟨r, ⟨mem, ⟨p, ⟨σ, ⟨h, eq⟩⟩⟩⟩⟩ := ih
    exists r; apply And.intro; trivial
    exists (left::p); exists σ; exists h
    simp [Rule.rewriteAt, substAt]
    simp [Rule.rewriteAt] at eq
    trivial
  case _ ih =>
    let ⟨r, ⟨mem, ⟨p, ⟨σ, ⟨h, eq⟩⟩⟩⟩⟩ := ih
    exists r; apply And.intro; trivial
    exists (right::p); exists σ; exists h
    simp [Rule.rewriteAt, substAt]
    simp [Rule.rewriteAt] at eq
    trivial

@[simp]
lemma Term.substAt_valid {t : Term} {p : Position}
  (h : p.valid t)
  : p.valid (t.substAt p h u) := by
  revert h
  match p, t with
  | [], _ => simp [valid]
  | left::_, _ @@ _ => simp [valid, substAt]; apply Term.substAt_valid
  | right::_, _ @@ _ => simp [valid, substAt]; apply Term.substAt_valid
  | left::_, var _ => simp [valid]
  | right::_, var _ => simp [valid]
  | left::_, func _ => simp [valid]
  | right::_, func _ => simp [valid]

-- A subtitution at an orthogonal position does not change validity
lemma Position.valid_substAt_of_ortho_left {p q : Position} (h₁ : p.valid t) (h₂ : q.valid t) (orth : p ⊥ q) :
  p.valid (t.substAt q h₂ u) := by
  revert h₁ h₂ orth
  match p, q, t with
  | [], _, _ => grind
  | _, [], _ => grind
  | m::p', n::q', t₁ @@ t₂ =>
    cases m <;> cases n <;> simp [valid, substAt] <;> try grind
    . apply Position.valid_substAt_of_ortho_left
    . apply Position.valid_substAt_of_ortho_left
  | _::_, _::_, var _ => grind
  | _::_, _::_, func _ => grind

lemma Position.valid_substAt_of_ortho_right {p q : Position} (h₁ : p.valid t) (h₂ : q.valid t) (orth : p ⊥ q) :
  q.valid (t.substAt p h₁ u) := by
  revert h₁ h₂ orth
  match p, q, t with
  | [], _, _ => grind
  | _, [], _ => grind
  | m::p', n::q', t₁ @@ t₂ =>
    cases m <;> cases n <;> simp [valid, substAt] <;> try grind
    . apply Position.valid_substAt_of_ortho_right
    . apply Position.valid_substAt_of_ortho_right
  | _::_, _::_, var _ => grind
  | _::_, _::_, func _ => grind

lemma Position.get_substAt_of_ortho_aux {p q : Position}
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (orth : p ⊥ q)
  (h₂' : q.valid (t.substAt p h₁ u))
 : q.get (t.substAt p h₁ u) h₂' = q.get t h₂ := by
  revert h₁ h₂ orth h₂'
  match p, q, t with
  | [], _, _ => simp [IsOrtho]
  | _, [], _ => simp [IsOrtho]
  | left::_, right::_, _ @@ _ =>
    simp [Position.get, Term.substAt]
  | right::_, left::_, _ @@ _ =>
    simp [Position.get, Term.substAt]
  | left::_, left::_, _ @@ _ =>
    simp [IsOrtho, Position.get, Term.substAt]
    intros; apply Position.get_substAt_of_ortho_aux; grind
  | right::_, right::_, _ @@ _ =>
    simp [IsOrtho, Position.get, Term.substAt]
    intros; apply Position.get_substAt_of_ortho_aux; grind
  | _::_, _::_, var _ => simp [valid]
  | _::_, _::_, func _ => simp [valid]


lemma Position.get_substAt_of_ortho {p q : Position}
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (orth : p ⊥ q)
  : q.get (t.substAt p h₁ u) (Position.valid_substAt_of_ortho_right h₁ h₂ orth) = q.get t h₂ := by
  grind [Position.get_substAt_of_ortho_aux]

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
  | [], _, _ => grind
  | _, [], _ => grind
  | m::p', n::q', t₁ @@ t₂ =>
    cases m <;> cases n <;> simp [valid, substAt] <;> intros
    . apply Term.substAt_comm_of_ortho_aux; trivial
    . apply Term.substAt_comm_of_ortho_aux; trivial
  | _::_, _::_, var _ => grind
  | _::_, _::_, func _ => grind

lemma Term.substAt_comm_of_ortho
  {p q : Position}
  (t u₁ u₂ : Term)
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (orth : p ⊥ q)
  : (t.substAt p h₁ u₁).substAt q (Position.valid_substAt_of_ortho_right h₁ h₂ orth) u₂ =
    (t.substAt q h₂ u₂).substAt p (Position.valid_substAt_of_ortho_left h₁ h₂ orth) u₁ := by
  grind [Term.substAt_comm_of_ortho_aux]

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
  grind [Rule.rewriteAt, Term.substAt_comm_of_ortho]

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
    . rw [← h₂]; simp [valid]; grind
    . rw [← h₂]; simp [valid]; grind

@[grind →]
lemma Position.get_eq_var_of_mem_varPos_aux
  (p : Position)
  (mem : p ∈ varPos t x)
  (h : p.valid t)
  : p.get t h = var x := by
  revert mem h p
  induction t <;> simp [varPos, valid]
  case _ =>
    intros eq
    simp [Position.get]; trivial
  case _ t₁ t₂ ih₁ ih₂ =>
    intros p shape
    rcases shape with ⟨a, h₁, h₂⟩ | ⟨a, h₁, h₂⟩
    . rw [← h₂]; simp [valid, Position.get]; grind
    . rw [← h₂]; simp [valid, Position.get]; grind

lemma Position.get_eq_var_of_mem_varPos {p : Position} (mem : p ∈ varPos t x)
  : p.get t (Position.valid_of_mem_varPos p mem) = var x := by
  grind [Position.get_eq_var_of_mem_varPos_aux]

lemma Position.mem_varPos_of_get_eq_var {p : Position} {h : p.valid t}
  (isVar : p.get t h = var x) : p ∈ varPos t x := by
  revert p
  induction t
  case _ y =>
    simp [varPos]; intros p
    cases p  -- <;> grind [Position.get] -- internal `grind` error, term has not been internalized valid (left :: tail) (t₁✝ @@ a✝)
    . simp [Position.get]
    . simp [valid]
  case _ => intros p; cases p <;> simp [Position.get]
  case _ =>
    intros p; cases p; simp [Position.get]
    case _ hd tail =>
      cases hd <;> simp [Position.get, varPos] <;> grind

-- Sheesh this is awkward
lemma Position.ortho_leaf
  (h₁ : p.valid t) (h₂ : q.valid t)
  (isVar₁ : p.get t h₁ |>.isVar)
  (isVar₂ : q.get t h₂ |>.isVar)
  (neq : p ≠ q) : p ⊥ q := by
  match p, q, t with
  | left::_, right::_, t₁ @@ t₂ => grind
  | right::_, left::_, t₁ @@ t₂ => grind
  | right::_, right::_, t₁ @@ t₂ =>
    simp; simp [Position.get] at isVar₁; simp [Position.get] at isVar₂; simp at neq
    apply Position.ortho_leaf (t:=t₂) <;> trivial
  | left::_, left::_, t₁ @@ t₂ =>
    simp; simp [Position.get] at isVar₁; simp [Position.get] at isVar₂; simp at neq
    apply Position.ortho_leaf (t:=t₁) <;> trivial
  | [], [], _ => grind
  | _::_, [], t₁ @@ t₂ => simp [isVar, Position.get] at isVar₂
  | [], _::_, t₁ @@ t₂ => simp [isVar, Position.get] at isVar₁
  | [], _ :: _, var _ => simp [valid] at h₂

lemma Position.ortho_varPos : ∀ p ∈ varPos t x, ∀ q ∈ varPos t x, p ≠ q → p ⊥ q := by
  intros p mem₁ q mem₂ neq; apply Position.ortho_leaf <;> try trivial
  . rw [Position.get_eq_var_of_mem_varPos_aux]
    . simp [isVar]
    . trivial
    . grind
  . rw [Position.get_eq_var_of_mem_varPos_aux]
    . simp [isVar]
    . trivial
    . grind

-- We used to need this now it's just for free...
lemma varPos_nodup : (varPos t x).Nodup := by
  cases t <;> simp [varPos]
  . grind
  . rw [List.nodup_append]
    constructor
    . rw [List.nodup_map_iff (f := fun l => left::l)]
      . apply varPos_nodup
      . simp
    . constructor
      . rw [List.nodup_map_iff (f := fun l => right::l)]
        . apply varPos_nodup
        . simp
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
  by_cases eq:(q = p); simp [eq]
  grind [Position.valid_substAt_of_ortho_right]

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

-- Need some algebraic fact about `(t₁ @@ t₂).substAll u (varPos (t₁ @@ t₂) x)`.
-- or just `(t₁ @@ t₂). substAll u |> (ps₁.map (left :: ·)) ++ (ps₂.map (right :: · ))`

private lemma substAllMapRight
  : (t₁ @@ t₂).substAll u (List.map (fun x => right :: x) ps) h' orth' =
    (t₁ @@ t₂.substAll u ps h orth) := by
  revert t₂
  induction ps <;> intros
  . simp; eq_refl -- proof irrelevance saves the day
  case _ ih _ _ _ =>
    simp [substAll, substAt]
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
  . simp [join, substAll]
    apply substAllMapRight
  case _ ih _ _ _ =>
    simp [join, substAll, substAt]
    apply ih -- again, proof irrelevance

theorem Term.substAll_eq_varSubst (t u : Term) (x : Var) :
  t.substAll u (varPos t x) Position.valid_of_mem_varPos Position.ortho_varPos =
  t.apply (varSubst x u) := by
  induction t
  case _ y =>
    simp [varPos, apply, varSubst]
    by_cases h:(y = x) <;> simp [h, substAll, substAt]
  case _ => simp [substAll, apply, varPos]
  case _ ih₁ ih₂ =>
    simp [varPos, apply]
    rw [substAllAppDecomp] -- now we pay the piper for all those hyps
    . congr
    . apply Position.valid_of_mem_varPos
    . apply Position.valid_of_mem_varPos
    . apply Position.ortho_varPos
    . apply Position.ortho_varPos

-- Since orthogonal substs commute, inserting a subst into the list is the same as doing it first

#check List.filter

-- let's first prove that rewriting at a variable reduces to rewriting at all positions of that var,
-- in 2 steps: first that rewriting at the position, then the rest of the list, is the
-- same as rewriting all at once. Then prove that a rewrite at any position is the same as
-- rewriting at some element of the `varPos` list.

lemma Term.substAt_idem {t : Term}
  (h : p.valid t)
  (h' : p.valid (t.substAt p h u)) -- this can be proven
  : (t.substAt p h u).substAt p h' u = t.substAt p h u := by
  match p, t with
  | [], _ => simp [substAt]
  | left::_, _@@_ => simp [substAt]; apply Term.substAt_idem
  | right::_, _@@_ => simp [substAt]; apply Term.substAt_idem

lemma Rule.rewriteAt_is_reduce {t : RTerm ℛ}
  {mem : ru ∈ ℛ}
  (h : p.valid t)
  (mtch : ru.matchesAt t p σ h)
  : t ~> ru.rewriteAt t p σ h := by
  revert mtch
  match p, t with
  | [], _ =>
    simp [Rule.matchesAt, Position.get, Rule.rewriteAt, substAt]
    intros h; simp [← h]
    apply Reduces.head; trivial
  | left::p', t₁ @@ _ =>
    simp [Rule.matchesAt, Position.get, Rule.rewriteAt, substAt]
    intro mtch; apply Reduces.congrLeft
    apply Rule.rewriteAt_is_reduce <;> trivial
  | right::p', _ @@ t₂ =>
    simp [Rule.matchesAt, Position.get, Rule.rewriteAt, substAt]
    intro mtch; apply Reduces.congrRight
    apply Rule.rewriteAt_is_reduce <;> trivial

@[simp]
def RTerm.substAt (t : RTerm ℛ) (p : Position) (h : p.valid t) (u : Term) : RTerm ℛ :=
  Term.substAt t p h u

@[simp]
lemma Term.get_substAt_of_valid : substAt t p h (p.get t h') = t := by
  revert h h'
  match p, t with
  | [], _ => simp [valid, substAt, Position.get]
  | left::_ , _@@_ => simp [valid, substAt, Position.get]; apply Term.get_substAt_of_valid
  | right::_ , _@@_ => simp [valid, substAt, Position.get]; apply Term.get_substAt_of_valid
  | _::_, var _ => simp [valid]
  | _::_, func _ => simp [valid]

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
    simp [substAt]; grind
  | left::p', t₁ @@ _ =>
    simp [Term.substAt, valid]; intros
    apply Reduces.congrLeft; apply Rule.rewriteAt_substAt; grind
  | right::p', _ @@ t₂ =>
    simp [Term.substAt, valid]; intros
    apply Reduces.congrRight; apply Rule.rewriteAt_substAt; grind
  | _::_, var _ => simp [valid]
  | _::_, func _ => simp [valid]

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
    simp [Rule.rewriteAt, ← idem]
  rw [← eq]
  apply refl_trans_clos.refl

#check Term.substAt_comm_of_ortho_aux

lemma Term.substAll_swap {t : Term}
  (orth : p ⊥ q)
  (allValid₁ : ∀ p' ∈ p::q::ps, p'.valid t)
  (allOrth₁ : ∀ p' ∈ p::q::ps, ∀ p'' ∈ p::q::ps, p' ≠ p'' → p' ⊥ p'')
  (allValid₂ : ∀ p' ∈ q::p::ps, p'.valid t)
  (allOrth₂ : ∀ p' ∈ q::p::ps, ∀ p'' ∈ q::p::ps, p' ≠ p'' → p' ⊥ p'')
  : t.substAll u (p::q::ps) allValid₁ allOrth₁ =
    t.substAll u (q::p::ps) allValid₂ allOrth₂ := by
  simp [substAll]
  congr 1
  apply Term.substAt_comm_of_ortho_aux; grind

lemma Term.substAll_idem {t : Term}
  (h₁ : ∀ p' ∈ ps, p'.valid t)
  (h₂ : ∀ p' ∈ p::ps, p'.valid t)
  (orth₁ : ∀ p' ∈ ps, ∀ p'' ∈ ps, p' ≠ p'' → p' ⊥ p'')
  (orth₂ : ∀ p' ∈ p::ps, ∀ p'' ∈ p::ps, p' ≠ p'' → p' ⊥ p'')
  (mem : p ∈ ps)
  : t.substAll u (p::ps) h₂ orth₂ = t.substAll u ps h₁ orth₁ := by
  revert t
  induction ps
  case _ => simp at mem
  case _ hd tail ih =>
    by_cases h:(p = hd)
    . simp [h, substAll, Term.substAt_idem]
    . intros
      have h' : p ⊥ hd := by grind
      rw [Term.substAll_swap] <;> try grind
      . simp [substAll]
        apply ih <;> try grind
        . simp; constructor
          . apply Position.valid_substAt_of_ortho_left <;> grind
          . grind [Term.substAt_valid_list]

#check Position.get_substAt_of_ortho

lemma Rule.rewriteAt_substAll_stutter {ℛ : Rules} {t u₁ u₂ : RTerm ℛ}
  (allValid : ∀ p ∈ ps, p.valid t)
  (mtch : ∀ p (mem : p ∈ ps),
    p.get t (allValid p mem) = u₁ ∨ p.get t (allValid p mem) = u₂)
  (red : u₁ ~> u₂)
  (allOrth : ∀ p ∈ ps, ∀ q ∈ ps, p ≠ q → (p ⊥ q))
  : t ~>* t.substAll u₂ ps allValid allOrth := by
  revert t
  induction ps
  . simp [refl_trans_clos.refl, substAll]
  case _ p ps ih =>
    intros t _ mtch
    simp [substAll]
    cases mtch p (by grind)
    case _ hl =>
      apply refl_trans_clos.step
       (b := t.substAt p (by grind) u₂)
      . apply Rule.rewriteAt_substAt_aux; trivial; grind
      . apply ih
        intros q mem
        by_cases eq:(p = q)
        . simp [eq]
        . have pq_orth : p ⊥ q := by grind
          simp
          rw [Position.get_substAt_of_ortho] <;> try grind
    case _ getEq =>
      rewrite (occs := .pos [1]) [← Term.get_substAt (t:=t) (p:=p)]
      rw [getEq]
      apply ih
      . intros q mem
        by_cases eq:(p = q)
        . simp [eq]
        . have pq_orth : p ⊥ q := by grind
          rw [Position.get_substAt_of_ortho] <;> try grind
      . grind

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
  simp [substAll]
  apply Rule.rewriteAt_substAll_stutter
  . intros q mem
    by_cases eq:(p = q)
    . simp [eq]
    . have pq_orth : p ⊥ q := by grind
      rw [Position.get_substAt_of_ortho] <;> try grind
      . left; apply mtch; trivial
  . trivial

#print Subst.join

-- Ok this is slightly too weak
#check Term.substAll_eq_varSubst

#check Position.valid_of_mem_varPos

def Subst.replace (σ : Subst) (x : Var) (u : Term) : Subst :=
  fun y => if y = x then u else σ y

lemma Term.substAll_eq_substAt (t u : Term) (x : Var) :
  (t.apply τ).substAll u (varPos t x) (by grind [Position.valid_of_mem_varPos, Position.valid_apply]) Position.ortho_varPos =
  t.apply (τ.replace x u) := by
  induction t
  case _ y =>
    simp [varPos, apply]
    by_cases h:(y = x) <;> simp [h, substAll, substAt, Subst.replace]
  case _ => simp [substAll, apply, varPos]
  case _ ih₁ ih₂ =>
    simp [varPos, apply]
    rw [substAllAppDecomp] -- now we pay the piper for all those hyps
    . congr
    . intros; grind [Position.valid_of_mem_varPos, Position.valid_apply]
    . intros; grind [Position.valid_of_mem_varPos, Position.valid_apply]
    . apply Position.ortho_varPos
    . apply Position.ortho_varPos

#check Rule.rewriteAt_substAll

lemma Position.get_apply {p : Position}
  (h : p.valid t)
  (h' : p.valid (t.apply σ))
  : p.get (t.apply σ) h' = (p.get t h).apply σ := by
  match p, t with
  | [], _ => simp [Position.get]
  | left::_, t₁ @@ _ => simp [apply, Position.get]; apply Position.get_apply
  | right::_, _ @@ t₂ => simp [apply, Position.get]; apply Position.get_apply
  | _::_, var _ => simp [valid] at h
  | _::_, func _ => simp [valid] at h

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
  simp [RTerm.apply]
  rw [← Term.substAll_eq_substAt t u₂ x (τ := τ)]
  -- Notations smotations
  have h₂ := Rule.rewriteAt_substAll
   (t := t.apply τ) (u₁ := u₁) (u₂ := u₂) (p := p) (ps := varPos t x)
  simp at h₂
  apply h₂
  . apply Position.mem_varPos_of_get_eq_var <;> grind
  . intros; rw [Position.get_apply]
    . rw [Position.get_eq_var_of_mem_varPos_aux]
      . simp [apply]; trivial
      . trivial
    . grind
  . trivial
  . grind [Position.valid_of_mem_varPos, Position.valid_apply]

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

#check Reduces.exists_rewriteAt
#check Position.trichotomy

#check Rule.rewriteAt_comm_of_ortho
#check Rule.rewriteAt_is_reduce
#check Position.get_substAt_of_ortho_aux

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
    simp [Rule.rewriteAt, Rule.matchesAt]
    rw [Position.get_substAt_of_ortho_aux]
    . apply mtch₂
    . trivial
    . trivial
  . apply refl_trans_clos.step _ _ _ _ (by apply refl_trans_clos.refl)
    rw [Rule.rewriteAt_comm_of_ortho] <;> try trivial
    apply Rule.rewriteAt_is_reduce; trivial
    simp [Rule.rewriteAt, Rule.matchesAt]
    rw [Position.get_substAt_of_ortho_aux]
    . apply mtch₁
    . trivial
    . apply Position.isOrtho_comm; trivial

#print PreCriticalPair

lemma Rule.matchesAt_head_iff {t : Term} {ru : Rule}
  (h : ru.matchesAt t [] σ (Eq.refl true))
  : t = ru.lhs.apply σ := by
  revert h
  simp [Rule.matchesAt, Position.get]
  grind

#check IsOuterPosition.exists_split
#check Rule.rewriteAt_var_eq_subst
#check Position.splitOnSubst_concat
#print substAt

lemma Position.valid_append {p₁ p₂ : Position}
  (h : (p₁ ++ p₂).valid t)
  : p₁.valid t := by
  revert h
  match p₁, t with
  | [], _ => simp [valid]
  | left::_, _ @@ _ => simp [valid]; apply Position.valid_append
  | right::_, _ @@ _ => simp [valid]; apply Position.valid_append
  | _::_, var _ => simp [valid]
  | _::_, func _ => simp [valid]

lemma Position.valid_appendGet {p₁ p₂ : Position}
  (h₁ : (p₁ ++ p₂).valid t)
  (h₂ : p₁.valid t)
  : p₂.valid (p₁.get t h₂) := by
  revert h₁ h₂
  match p₁, t with
  | [], _ => simp [valid, Position.get]
  | left::_, _ @@ _ => simp [valid]; apply Position.valid_appendGet
  | right::_, _ @@ _ => simp [valid]; apply Position.valid_appendGet
  | _::_, var _ => simp [valid]
  | _::_, func _ => simp [valid]

lemma Term.substAt_append {p₁ p₂ : Position}
  (h₁ : p₁.valid t)
  (h₂ : p₂.valid (p₁.get t h₁))
  (h₃ : (p₁ ++ p₂).valid t)
  : substAt t (p₁ ++ p₂) h₃ u = substAt t p₁ h₁ (substAt (p₁.get t h₁) p₂ h₂ u) := by
  revert h₁
  match p₁, t with
  | [], _ => simp [Position.get, substAt]
  | left::_, _ @@ _ => simp [substAt, Position.get]; intros; apply Term.substAt_append
  | right::_, _ @@ _ => simp [substAt, Position.get]; intros; apply Term.substAt_append
  | _::_, var _ => simp [valid]
  | _::_, func _ => simp [valid]

lemma Rule.matchesAt_append {p₁ p₂ : Position} {ru : Rule}
  (h₁ : p₁.valid t)
  (h₂ : p₂.valid (p₁.get t h₁))
  (h₃ : (p₁ ++ p₂).valid t)
  (mtchConcat : ru.matchesAt t (p₁ ++ p₂) σ h₃)
  : ru.matchesAt (p₁.get t h₁) p₂ σ h₂ := by
  revert mtchConcat
  simp [Rule.matchesAt]

#check Rule.rewriteAt_is_reduce
#check Rule.rewriteAt_var_eq_subst

lemma Rule.rewriteAt_replace {t : RTerm ℛ}
  (rewAt : let u' : RTerm ℛ := σ x; u' ~> u)
  : t.apply σ ~>* t.apply (σ.replace x u) := by
  induction t
  case _ y =>
    by_cases h:(y = x)
    . simp [h, RTerm.apply, apply, Subst.replace]
      apply refl_trans_clos.step _ _ _ _ (by apply refl_trans_clos.refl)
      trivial
    . simp [RTerm.apply, apply, Subst.replace]
      simp [h]
      apply refl_trans_clos.refl
  case _ => simp [apply]; apply refl_trans_clos.refl
  case _ =>
    simp [apply]
    apply Reduces.refl_trans_clos_congr <;> trivial

lemma IsNotOuterValid {p : Position}
  (h : p.valid <| t.apply σ)
  (isNOuter : ¬ IsOuterPosition p t σ)
  : p.valid t  := by
  revert h isNOuter
  match p, t with
  | [], _ => simp [valid]
  | left::_, _ @@ _ =>
    simp [valid, apply, IsOuterPosition, splitOnSubst, Position.get]
    intros; apply IsNotOuterValid
    . trivial
    . simp [IsOuterPosition]; grind
  | right::_, _ @@ _ =>
    simp [valid, apply, IsOuterPosition, splitOnSubst, Position.get]
    intros; apply IsNotOuterValid
    . trivial
    . simp [IsOuterPosition]; grind
  | _::_, var _ =>
    simp [IsOuterPosition, splitOnSubst, Position.get, valid, Term.isVar]
  | _::_, func _ =>
    simp [valid, apply]

-- FIXME: this is a dumb proof, could just induct on `t`.
lemma IsNotOuterNvar_aux
  (h : p.valid t)
  (isNOuter : ¬ IsOuterPosition p t σ)
  : (p.get t h |>.isVar) = false := by
  revert h isNOuter
  match p, t with
  | [], _ => simp [valid, IsOuterPosition]
  | left::_, _ @@ _ =>
    simp [valid, IsOuterPosition, splitOnSubst, Position.get]
    intros; apply IsNotOuterNvar_aux
    . simp [IsOuterPosition]; trivial
  | right::_, _ @@ _ =>
    simp [valid, IsOuterPosition, splitOnSubst, Position.get]
    intros; apply IsNotOuterNvar_aux
    . simp [IsOuterPosition]; trivial
  | _::_, var _ =>
    simp [valid]
  | _::_, func _ =>
    simp [valid]

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
    simp [Rule.rewriteAt]
    have h₁₁ : p₁.valid t := by apply Position.valid_append; trivial
    have h₁₂ : p₂'.valid (p₁.get t h₁₁) := by apply Position.valid_appendGet; trivial
    rw [Term.substAt_append (t:=t) (h₁ := h₁₁) (h₂ := h₁₂)]
    let u : RTerm ℛ := (p₁.get t h₁₁).substAt p₂' h₁₂ (ru₂.rhs.apply σ₂)
    let u_l : RTerm ℛ := σ₁ x
    have h₅ : σ₁ x = p₁.get t h₁₁ := by
      calc
        σ₁ x = (var x).apply σ₁ := by simp [apply]
        _    = (p₁.get ru₁.lhs h).apply σ₁ := by rw [← h'']
        _    = (p₁.get (ru₁.lhs.apply σ₁) (Position.valid_apply σ₁ h)) := by rw [Position.get_apply]
        _    = (p₁.get t h₁₁) := by congr
    have u_rew : u_l ~> u := by -- This is the most finicky proof I have ever done
      simp [Rule.matchesAt] at mtch₂
      have h₃ : p₂'.valid u_l := by
        simp [Rule.matchesAt, Position.get] at mtch₁
        simp [u_l]
        have h₄ := Position.valid_append_right h₂
        rw [h₅]; trivial
      simp [u_l, u]; rw [h₅]
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
      simp [Rule.matchesAt, Position.get] at mtch₁
      simp [← mtch₁]; simp [u']
      . apply Rule.rewriteAt_var_eq_subst <;> trivial
      . simp [u']
        apply refl_trans_clos.step _ _ _ _ (by apply refl_trans_clos.refl)
        simp [Red.reduces]; apply Reduces.head
        trivial
  . simp [PreCriticalPair.joins] at joinable
    let cp : PreCriticalPair ℛ := by
      apply PreCriticalPair.mk ru₁ ru₂ mem₁ mem₂ σ₁ σ₂ p₂
      . apply IsNotOuterNvar; trivial
      . simp [Rule.matchesAt, Position.get] at mtch₁
        simp [mtch₁]
        trivial
      . simp [Rule.matchesAt, Position.get] at mtch₁
        rw [← mtch₁] at h₂
        apply IsNotOuterValid <;> trivial
    have joins := joinable cp
    simp [cp] at joins
    simp [Rule.rewriteHead, Rule.rewriteAt]
    simp [Rule.matchesAt, Position.get] at mtch₁
    simp [← mtch₁]
    apply joins

lemma joins_congr_left {t₁ t₂ u : RTerm ℛ}
  (joins : t₁ ~>*.*<~ t₂)
  : (t₁ @@@ u) ~>*.*<~ (t₂ @@@ u) := by
  have ⟨t', _⟩ := joins
  exists (t' @@@ u); grind [Reduces.refl_trans_clos_congr_left]

lemma joins_congr_right {t u₁ u₂ : RTerm ℛ}
  (joins : u₁ ~>*.*<~ u₂)
  : (t @@@ u₁) ~>*.*<~ (t @@@ u₂) := by
  have ⟨u', _⟩ := joins
  exists (t @@@ u'); grind [Reduces.refl_trans_clos_congr_right]

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
    simp [Rule.rewriteHead] at h
    simp [Rule.rewriteAt, substAt]
    apply h <;> trivial
  | left::p₁', left::p₂' =>
    cases t
    case _ => simp [valid] at h₁
    case _ => simp [valid] at h₁
    case _ =>
      simp [Rule.rewriteAt, substAt]
      apply joins_congr_left
      apply joinable_mono <;> trivial
  | right::p₁', right::p₂' =>
    cases t
    case _ => simp [valid] at h₁
    case _ => simp [valid] at h₁
    case _ =>
      simp [Rule.rewriteAt, substAt]
      apply joins_congr_right
      apply joinable_mono <;> trivial
  | left::p₁', right::p₂' => simp [Subset, Inc] at inc
  | right::p₁', left::p₂' => simp [Subset, Inc] at inc


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
  . rw [rew₁, rew₂]; apply joinable_mono <;> grind
  . rw [rew₁, rew₂]; apply joins_comm; apply joinable_mono <;> grind
  . rw [rew₁, rew₂]; apply joinable_of_ortho <;> grind

#print Finset.map
#print Var
#print String
#check String.ofList

-- breaks abstraction.
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

#check String.drop

-- Jeesh
def freshVarInv (renamed : Var) (avoid : Finset Var) : Var :=
  if h: avoid.Nonempty then
    let dropLen := getStringPrefix avoid h |>.length
    renamed |>.toList.drop dropLen |> String.ofList
  else
    renamed

#check Finset.mem_image_of_mem
#check String.length_append
#check Finset.max'_eq_iff

lemma freshVar_not_mem
  : freshVar x S ∉ S := by
  simp [freshVar]
  by_cases h:(S.Nonempty) <;> simp [h]
  . simp [getStringPrefix]
    intro h'
    have h' := Finset.mem_image_of_mem String.length h'
    simp at h'
    have ⟨a, h'⟩ := h'
    have h'' : ∀ b ∈ S, b.length < (Finset.image String.length S).max' (by simp; exact h) + 1 := by
      intros b mem
      have h : (String.length b ∈ Finset.image String.length S) := by simp [Finset.mem_image]; exists b
      have h := Finset.le_max' _ _ h
      grind
    have h'' := h'' a h'.1
    grind
  . simp at h; simp [h]

#check List.drop_append_length
#check String.ofList_append
#check String.ofList_toList
#check String.toList_ofList
#check List.toString

lemma freshVar_inv_inv :
  freshVarInv (freshVar x S) S = x := by
  simp [freshVar, freshVarInv]
  by_cases h:S.Nonempty <;> simp [h]

lemma freshVar_distinct
  (neq : x ≠ y)
  : freshVar x S ≠ freshVar y S := by
  intro h
  have h' : freshVarInv (freshVar x S) S = freshVarInv (freshVar y S) S := by grind
  grind [freshVar_inv_inv]

def Subst.ren (avoid : Finset Var) : Subst := fun x => var <| freshVar x avoid

#print Subst.scomp
#check Subst.scomp_apply

def Subst.joinAvoiding (σ₁ : Subst) (σ₂ : Subst) (S : Finset Var) : Subst :=
  fun x => if x ∈ S then σ₂ x else σ₁ (freshVarInv x S)

lemma Subst.join_apply_left (σ₁ : Subst) (σ₂ : Subst)
  : (Subst.ren S).scomp (σ₁.joinAvoiding σ₂ S) = σ₁ := by
  funext x; simp [Subst.scomp, Subst.ren, apply, Subst.joinAvoiding]
  simp [freshVar_not_mem, freshVar_inv_inv]

lemma Subst.join_apply_right {t : Term} {σ₁ σ₂ : Subst}
  {S : Finset Var}
  (h : t.vars ⊆ S)
  : t.apply (σ₁.joinAvoiding σ₂ S) = t.apply σ₂ := by
  revert h
  induction t
  case var x => simp [vars, apply, Subst.joinAvoiding]; grind
  case func _ => simp [apply]
  case app h₁ h₂ => simp [apply, vars]; grind


-- FIXME: is this the right lemma?
lemma Rule.matches_unifies {t₁ t₂ : Term}
  (h : t₁.apply σ₁ = t₂.apply σ₂)
  (h' : t₂.vars ⊆ S)
  : Unifier (σ₁.joinAvoiding σ₂ S) (t₁.apply <| Subst.ren S) t₂ := by
  simp [Unifier]
  rw [← Subst.scomp_apply]
  simp [Subst.join_apply_left]
  rw [Subst.join_apply_right] <;> grind


lemma Rule.match_unify {t₁ t₂ : Term}
  (h : t₁.apply σ₁ = t₂.apply σ₂)
  (_ : t₂.vars ⊆ S)
  : Unify (t₁.apply <| Subst.ren S) t₂ := by
  exists σ₁.joinAvoiding σ₂ S
  apply Rule.matches_unifies <;> trivial

#check unify_complete


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

#print PreCriticalPair

lemma unif_crit_isSome
  (cp : PreCriticalPair ℛ)
  : (unify ((cp.p.get cp.r₁.lhs cp.valid_p).apply (Subst.ren <| cp.r₂.lhs.vars ∪ cp.r₂.rhs.vars))
            cp.r₂.lhs).isSome := by
  apply unify_progress
  apply Rule.matches_unifies
  . have h := cp.mtch₂
    simp [Rule.matchesAt] at h
    rw [← Position.get_apply, h]
  . simp

def critical_of_preCritical (cp : PreCriticalPair ℛ) : CriticalPair ℛ :=
  CriticalPair.mk
    cp.r₁
    cp.r₂
    cp.mem₁
    cp.mem₂
    cp.p
    cp.valid_p
    (unif_crit_isSome cp)

#check unify_complete'
#check Reduces.refl_trans_clos_apply

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
  | [], _ => simp [substAt]
  | left::_, _ @@ _ => simp [apply, substAt, valid]; apply Term.apply_substAt
  | right::_, _ @@ _ => simp [apply, substAt, valid]; apply Term.apply_substAt
  | _::_, var _ => simp [valid]
  | _::_, func _ => simp [valid]

lemma joins_apply {t u : RTerm ℛ}
  (joins_t_u : t ~>*.*<~ u)
  : t.apply σ ~>*.*<~ u.apply σ := by
  have ⟨v, _⟩ := joins_t_u
  simp [joins]; exists (v.apply σ)
  apply And.intro <;> apply Reduces.refl_trans_clos_apply <;> grind

lemma JoinsCPImpJoinsPC
  (cp : PreCriticalPair ℛ)
  (joins : (critical_of_preCritical cp).joins)
  : cp.joins := by
  cases cp
  case _ r₁ r₂ mem₁ mem₂ σ₁ σ₂ p valid_p nvar mtch =>
  simp [critical_of_preCritical, CriticalPair.joins] at joins
  simp [PreCriticalPair.joins]
  simp [Rule.matchesAt] at mtch
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
  simp [Subst.scomp_apply]
  rw [isUnif]
  simp [Subst.scomp_apply] -- horror!!!!
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
  grind [JoinsCPImpJoinsPC]

import Traat.chapter3

section Position

#print Option

inductive Move where | left | right

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
lemma varValidHead (h : p.valid (var x)) : p = Position.head := by
  revert h; induction p <;> grind [Position.valid]

@[simp, grind .]
lemma funcValidHead (h : p.valid (func x)) : p = Position.head := by
  revert h; induction p <;> grind [Position.valid]


lemma Position.validSubst (p : Position) (t : Term) (σ : Subst)
  (h : p.valid t)
  : p.valid <| t.apply σ := by
  match p, t with
  | [], _ => simp [valid]
  | left::ps, t₁ @@ t₂ =>
    simp [apply, valid]; apply Position.validSubst
    . simp [valid] at h; trivial
  | right::ps, t₁ @@ t₂ =>
    simp [apply, valid]; apply Position.validSubst
    . simp [valid] at h; trivial
  | _::_, var _ => simp [valid] at h
  | _::_, func _ => simp [valid] at h

lemma validAppend {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : p₁.valid t := by
  revert h
  match p₁, t with
  | [], _ => simp [Position.valid]
  | left::_, t₁ @@ _ => simp [Position.valid]; intro h; apply validAppend h
  | right::_, _ @@ t₂ => simp [Position.valid]; intro h; apply validAppend h
  | _::_, var _ => simp [Position.valid]
  | _::_, func _ => simp [Position.valid]

lemma validAppendTail {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : p₂.valid <| p₁.get t (validAppend h) := by
  revert h
  match p₁, t with
  | [], _ => simp [Position.valid, Position.get]
  | left::_, t₁ @@ _ => simp [Position.valid, Position.get]; intro h; apply validAppendTail h
  | right::_, _ @@ t₂ => simp [Position.valid, Position.get]; intro h; apply validAppendTail h
  | _::_, var _ => simp [Position.valid]
  | _::_, func _ => simp [Position.valid]

@[simp]
lemma getAppend {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : (p₁ ++ p₂).get t h = p₂.get (p₁.get t <| validAppend h) (validAppendTail h) := by
  revert h
  match p₁, t with
  | [], _ => simp [Position.valid, Position.get]
  | left::_, t₁ @@ _ => simp [Position.valid, Position.get]; intro h; apply getAppend h
  | right::_, _ @@ t₂ => simp [Position.valid, Position.get]; intro h; apply getAppend h
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
lemma splitOnSubstHead : Position.splitOnSubst [] t σ = ([], []) := by
  induction t <;> simp [Position.splitOnSubst]

lemma splitOnSubstValid {p : Position} (h : p.valid (t.apply σ))
  : (p.splitOnSubst t σ).fst |>.valid t := by
  revert h
  match p, t with
  | [], _ => simp [Position.valid]
  | left::p', t₁ @@ _ =>
    simp [Position.splitOnSubst, apply, Position.valid]
    intros; apply splitOnSubstValid; grind
  | right::p', _ @@ t₂ =>
    simp [Position.splitOnSubst, apply, Position.valid]
    intros; apply splitOnSubstValid; grind
  | _, var _ =>
    simp [Position.valid, Position.splitOnSubst, apply]
  | _, func _ =>
    simp [Position.valid, Position.splitOnSubst, apply]

lemma splitOnSubstConcat {p : Position}
 : (p.splitOnSubst t σ).1 ++ (p.splitOnSubst t σ).2 = p := by
  match p, t with
  | [], _ => simp
  | left::p', t₁ @@ _ =>
    simp [Position.splitOnSubst]
    apply splitOnSubstConcat
  | right::p', _ @@ t₂ =>
    simp [Position.splitOnSubst]
    apply splitOnSubstConcat
  | _, var _ =>
    simp [Position.splitOnSubst]
  | _, func _ =>
    simp [Position.splitOnSubst]

-- A rewrite at a position that satisfies this predicate is "inner", that is
-- it occurs only within substituted terms.
def IsInnerPosition (p : Position) (t : Term) (σ : Subst) : Bool :=
  let ⟨p, _⟩ := p.splitOnSubst t σ
  if h : (p.valid t) then p.get t h |>.isVar else false

-- define subst-at, rewrite-at, prove that you can always replace a rewrite with a rewrite at

def Term.substAt (t : Term) (p : Position) (h : p.valid t) (u : Term) : Term :=
match p, t with
| [], _ => u
| left::p', t₁ @@ t₂ => (Term.substAt t₁ p' h u) @@ t₂
| right::p', t₁ @@ t₂ => t₁ @@ (Term.substAt t₂ p' h u)
| _::_, var _ => by simp [Position.valid] at h
| _::_, func _ => by simp [Position.valid] at h

lemma validSubstAt {p : Position} (h : p.valid t)
  : p.valid (t.substAt p h u) := by
  revert h
  match p, t with
  | [], _ => simp [Position.valid]
  | left::p', t₁ @@ _ =>
    simp [Position.valid, substAt]
    apply validSubstAt
  | right::p', _ @@ t₂ =>
    simp [Position.valid, substAt]
    apply validSubstAt
  | _::_, var _ => simp [Position.valid, substAt]
  | _::_, func _ => simp [Position.valid, substAt]

@[simp]
lemma substAtget {t : Term} {p : Position} (h : p.valid t)
 : p.get (t.substAt p h u) (validSubstAt h) = u := by
  revert h
  match p, t with
  | [], _ => simp [Position.valid, substAt, Position.get]
  | left::p', t₁ @@ _ =>
    simp [Position.valid, substAt, substAt]
    apply substAtget
  | right::p', _ @@ t₂ =>
    simp [Position.valid, substAt, substAt]
    apply substAtget
  | _::_, var _ => simp [Position.valid, substAt]
  | _::_, func _ => simp [Position.valid, substAt]

def Position.Inc (p q : Position) : Bool :=
match p, q with
| [], _ => true
| left::p', left::q' => Position.Inc p' q'
| right::p', right::q' => Position.Inc p' q'
| _, _ => false

#print HasSubset

instance Position.instHasSubset : HasSubset Position where
  Subset p q := Position.Inc p q

-- A little tedium here
@[grind →]
lemma validInc {p q : Position} (h : q.valid t) (inc : p ⊆ q)
 : p.valid t := by
  revert inc h; simp [Subset]
  match p, q, t with
  | [], _, _ => simp [Position.valid]
  | left::p', left::q', t₁ @@ _ =>
    simp [Position.valid, Position.Inc]
    apply validInc
  | right::p', right::q', _ @@ t₂ =>
    simp [Position.valid, Position.Inc]
    apply validInc
  | _, _::_, var _ => simp [Position.valid]
  | _, _::_, func _ => simp [Position.valid]
  | _::_, [], _ => simp [Position.Inc]
  | right::_, left::_, _ => simp [Position.Inc]
  | left::_, right::_, _ => simp [Position.Inc]


#print Reduces
#print Rules
#print Rule

-- This is a compbination of `Reduces.subst` and `Reduces.ax`.
@[simp]
def Rule.matchesHead (r : Rule) (t : Term) (σ : Subst) : Prop :=
  r.lhs.apply σ = t

-- Hey we don't even need the term here!
@[simp]
def Rule.rewriteHead (r : Rule) (σ : Subst) : Term := r.rhs.apply σ

-- A little awkward to have to bundle the `p.valid t` proof here.
def Rule.matchesAt (r : Rule) (t : Term) (p : Position) (σ : Subst) (h : p.valid t) : Prop :=
  r.matchesHead (p.get t h) σ

def Rule.rewriteAt (r : Rule) (t : Term) (p : Position) (σ : Subst) (h : p.valid t) : Term :=
  t.substAt p h (r.rewriteHead σ)

-- This is our master theorem to move between the "nice" definition of rewriting to the
-- position based one, which will allow us to do horrible reasoning about critical pairs.
theorem rewriteIsRewriteAt {ℛ : Rules} (t t' : RTerm ℛ) (red : t ~> t')
 : ∃ r ∈ ℛ, ∃ (p : Position) (σ : Subst) (h : p.valid t), t' = r.rewriteAt t p σ h := by
  simp [Red.reduces] at red
  induction red
  case _ l r σ mem =>
    exists ⟨l, r⟩; apply And.intro; trivial
    exists []; exists σ; exists rfl
    simp [Rule.rewriteAt, substAt]
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

end Position

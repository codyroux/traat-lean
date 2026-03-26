import Traat.chapter3

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

-- A rewrite at a position that satisfies this predicate is "outer", that is
-- it occurs only within substituted terms.
def IsOuterPosition (p : Position) (t : Term) (σ : Subst) : Bool :=
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

@[simp]
lemma subsetHead {p : Position} : [] ⊆ p := by
  simp [Subset, Position.Inc]

@[simp]
lemma subsetNotHead {p : Position} : ¬ m::p ⊆ [] := by
  simp [Subset, Position.Inc]

@[simp]
lemma subsetTail {p q : Position} : (m::p ⊆ m::q) = (p ⊆ q) := by
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
lemma subsetNotTail {p q : Position} (h : m ≠ n) : ¬ (m::p ⊆ n::q) := by
  revert h
  cases m <;> cases n <;> simp [Subset, Position.Inc]

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
lemma sdiffHead₁ {p : Position} : p \ [] = p := by
  induction p <;> simp [Position.instSDiff, Position.sdiff]

@[simp]
lemma sdiffHead₂ {p : Position} : [] \ p = [] := by
  induction p <;> simp [Position.instSDiff, Position.sdiff]

@[simp]
lemma sdiffCons {p q : Position} {m : Move} : (m::p) \ (m::q) = p \ q := by
  cases m <;> simp [Position.instSDiff, Position.sdiff]

@[simp]
lemma sdiffEmpty {p : Position} : (p \ p) = [] := by
  induction p <;> simp; trivial

lemma sdiffSum {p q : Position} (inc : p ⊆ q) : q = p ++ (q \ p) := by
  revert inc
  cases p <;> cases q <;> simp
  case cons.cons m _ n _ =>
    by_cases h:(m = n)
    . simp [h]; apply sdiffSum
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
lemma isOrthoCons (h : m ≠ n) : (m::p) ⊥ (n::q) := by
  revert h; cases m <;> cases n <;> simp [Position.IsOrtho]

@[simp]
lemma isOrthoCons' : ((m::p) ⊥ (m::q)) = (p ⊥ q) := by
  cases m <;> simp only [Position.IsOrtho]

@[grind .]
lemma isOrthoNil : ¬ ([] ⊥ p) := by
  cases p <;> simp [Position.IsOrtho]

@[grind .]
lemma isOrthoNil' : ¬ (p ⊥ []) := by
  cases p <;> simp [Position.IsOrtho]

lemma trichotomy {p q : Position} : p ⊆ q ∨ q ⊆ p ∨ p ⊥ q := by
  cases p <;> cases q <;> try simp
  case cons.cons m _ n _ =>
    by_cases h:(m = n)
    . simp [h]; apply trichotomy
    . grind

end Position

open Position Move Term

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

def Rule.rewriteAt
  (r : Rule)
  (t : RTerm ℛ)
  (p : Position)
  (σ : Subst) (h : p.valid t) : RTerm ℛ :=
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
    simp [Rule.rewriteAt, Term.substAt]
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
lemma substValid {t : Term} {p : Position}
  (h : p.valid t)
  : p.valid (t.substAt p h u) := by
  revert h
  match p, t with
  | [], _ => simp [valid]
  | left::_, _ @@ _ => simp [valid, substAt]; apply substValid
  | right::_, _ @@ _ => simp [valid, substAt]; apply substValid
  | left::_, var _ => simp [valid]
  | right::_, var _ => simp [valid]
  | left::_, func _ => simp [valid]
  | right::_, func _ => simp [valid]

-- A subtitution at an orthogonal position does not change validity
lemma orthValidL {p q : Position} (h₁ : p.valid t) (h₂ : q.valid t) (orth : p ⊥ q) :
  p.valid (t.substAt q h₂ u) := by
  revert h₁ h₂ orth
  match p, q, t with
  | [], _, _ => grind
  | _, [], _ => grind
  | m::p', n::q', t₁ @@ t₂ =>
    cases m <;> cases n <;> simp [valid, substAt] <;> try grind
    . apply orthValidL
    . apply orthValidL
  | _::_, _::_, var _ => grind
  | _::_, _::_, func _ => grind

lemma orthValidR {p q : Position} (h₁ : p.valid t) (h₂ : q.valid t) (orth : p ⊥ q) :
  q.valid (t.substAt p h₁ u) := by
  revert h₁ h₂ orth
  match p, q, t with
  | [], _, _ => grind
  | _, [], _ => grind
  | m::p', n::q', t₁ @@ t₂ =>
    cases m <;> cases n <;> simp [valid, substAt] <;> try grind
    . apply orthValidR
    . apply orthValidR
  | _::_, _::_, var _ => grind
  | _::_, _::_, func _ => grind

lemma substAtgetOrth' {p q : Position}
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
    intros; apply substAtgetOrth'; grind
  | right::_, right::_, _ @@ _ =>
    simp [IsOrtho, Position.get, Term.substAt]
    intros; apply substAtgetOrth'; grind
  | _::_, _::_, var _ => simp [valid]
  | _::_, _::_, func _ => simp [valid]


lemma substAtgetOrth {p q : Position}
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (orth : p ⊥ q)
  : q.get (t.substAt p h₁ u) (orthValidR h₁ h₂ orth) = q.get t h₂ := by
  grind [substAtgetOrth']

lemma substOrth'
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
    . apply substOrth'; trivial
    . apply substOrth'; trivial
  | _::_, _::_, var _ => grind
  | _::_, _::_, func _ => grind

lemma substOrth
  {p q : Position}
  (t u₁ u₂ : Term)
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (orth : p ⊥ q)
  : (t.substAt p h₁ u₁).substAt q (orthValidR h₁ h₂ orth) u₂ =
    (t.substAt q h₂ u₂).substAt p (orthValidL h₁ h₂ orth) u₁ := by
  grind [substOrth']

-- rewriting at orthogonal positions commutes
-- FIXME: rename this
lemma orthCommutes
  {ru₁ ru₂ : Rule}
  {p q : Position}
  (t : RTerm ℛ)
  (h₁ : p.valid t)
  (h₂ : q.valid t)
  (orth : p ⊥ q)
  : ru₂.rewriteAt (ru₁.rewriteAt t p σ h₁) q τ (orthValidR h₁ h₂ orth) =
    ru₁.rewriteAt (ru₂.rewriteAt t q τ h₂) p σ (orthValidL h₁ h₂ orth) := by
  grind [Rule.rewriteAt, substOrth]

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
lemma isValidVarPos : ∀ p ∈ varPos t x, p.valid t := by
  induction t <;> simp [varPos, valid]
  case _ t₁ t₂ ih₁ ih₂ =>
    intros p shape
    rcases shape with ⟨a, h₁, h₂⟩ | ⟨a, h₁, h₂⟩
    . rw [← h₂]; simp [valid]; grind
    . rw [← h₂]; simp [valid]; grind

@[grind →]
lemma isVarVarPos'
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

lemma isVarVarPos {p : Position} (mem : p ∈ varPos t x)
  : p.get t (isValidVarPos p mem) = var x := by
  grind [isVarVarPos']

lemma varPosComplete {p : Position} {h : p.valid t}
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
lemma orthLeaf
  (h₁ : p.valid t) (h₂ : q.valid t)
  (isVar₁ : p.get t h₁ |>.isVar)
  (isVar₂ : q.get t h₂ |>.isVar)
  (neq : p ≠ q) : p ⊥ q := by
  match p, q, t with
  | left::_, right::_, t₁ @@ t₂ => grind
  | right::_, left::_, t₁ @@ t₂ => grind
  | right::_, right::_, t₁ @@ t₂ =>
    simp; simp [Position.get] at isVar₁; simp [Position.get] at isVar₂; simp at neq
    apply orthLeaf (t:=t₂) <;> trivial
  | left::_, left::_, t₁ @@ t₂ =>
    simp; simp [Position.get] at isVar₁; simp [Position.get] at isVar₂; simp at neq
    apply orthLeaf (t:=t₁) <;> trivial
  | [], [], _ => grind
  | _::_, [], t₁ @@ t₂ => simp [isVar, Position.get] at isVar₂
  | [], _::_, t₁ @@ t₂ => simp [isVar, Position.get] at isVar₁

lemma orthVarPos : ∀ p ∈ varPos t x, ∀ q ∈ varPos t x, p ≠ q → p ⊥ q := by
  intros p mem₁ q mem₂ neq; apply orthLeaf <;> try trivial
  . rw [isVarVarPos']
    . simp [isVar]
    . trivial
    . grind
  . rw [isVarVarPos']
    . simp [isVar]
    . trivial
    . grind

-- We used to need this now it's just for free...
lemma nodupVarPos : (varPos t x).Nodup := by
  cases t <;> simp [varPos]
  . grind
  . rw [List.nodup_append]
    constructor
    . rw [List.nodup_map_iff (f := fun l => left::l)]
      . apply nodupVarPos
      . simp
    . constructor
      . rw [List.nodup_map_iff (f := fun l => right::l)]
        . apply nodupVarPos
        . simp
      . simp only [List.mem_map,
         ne_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
         List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true,
         implies_true] -- holy crap

lemma substValidList {p : Position} {ps : List Position}
  (h : p.valid t)
  (h' : ∀ q ∈ ps, q.valid t)
  (orth : ∀ q ∈ ps, p ≠ q → p ⊥ q)
  (mem : q ∈ ps)
  : q.valid (t.substAt p h u) := by
  by_cases eq:(q = p); simp [eq]
  grind [orthValidR]

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
      (by grind [substValidList])
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

theorem substAllIsVarSubst (t u : Term) (x : Var) :
  t.substAll u (varPos t x) isValidVarPos orthVarPos =
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
    . apply isValidVarPos
    . apply isValidVarPos
    . apply orthVarPos
    . apply orthVarPos

-- Since orthogonal substs commute, inserting a subst into the list is the same as doing it first

#check List.filter

-- let's first prove that rewriting at a variable reduces to rewriting at all positions of that var,
-- in 2 steps: first that rewriting at the position, then the rest of the list, is the
-- same as rewriting all at once. Then prove that a rewrite at any position is the same as
-- rewriting at some element of the `varPos` list.

lemma substAtIdem {t : Term}
  (h : p.valid t)
  (h' : p.valid (t.substAt p h u)) -- this can be proven
  : (t.substAt p h u).substAt p h' u = t.substAt p h u := by
  match p, t with
  | [], _ => simp [substAt]
  | left::_, _@@_ => simp [substAt]; apply substAtIdem
  | right::_, _@@_ => simp [substAt]; apply substAtIdem

lemma rewriteAtIsRewrite {t : RTerm ℛ}
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
    apply rewriteAtIsRewrite <;> trivial
  | right::p', _ @@ t₂ =>
    simp [Rule.matchesAt, Position.get, Rule.rewriteAt, substAt]
    intro mtch; apply Reduces.congrRight
    apply rewriteAtIsRewrite <;> trivial

@[simp]
lemma substAtGet : substAt t p h (p.get t h) = t := by
  revert h
  match p, t with
  | [], _ => simp [valid, substAt, Position.get]
  | left::_ , _@@_ => simp [valid, substAt, Position.get]; apply substAtGet
  | right::_ , _@@_ => simp [valid, substAt, Position.get]; apply substAtGet
  | _::_, var _ => simp [valid]
  | _::_, func _ => simp [valid]

-- A no-op substitution is a rewrite
lemma rewriteAtIsRewrite' {t : RTerm ℛ}
  {_ : ru ∈ ℛ}
  (h : p.valid t)
  (idem : p.get t h = ru.rhs.apply σ)
  : t ~>* ru.rewriteAt t p σ h := by
  have eq : t = ru.rewriteAt t p σ h := by
    simp [Rule.rewriteAt, ← idem]
  rw [← eq]
  apply refl_trans_clos.refl

#check substOrth'

lemma substAllSwap {t : Term}
  (orth : p ⊥ q)
  (allValid₁ : ∀ p' ∈ p::q::ps, p'.valid t)
  (allOrth₁ : ∀ p' ∈ p::q::ps, ∀ p'' ∈ p::q::ps, p' ≠ p'' → p' ⊥ p'')
  (allValid₂ : ∀ p' ∈ q::p::ps, p'.valid t)
  (allOrth₂ : ∀ p' ∈ q::p::ps, ∀ p'' ∈ q::p::ps, p' ≠ p'' → p' ⊥ p'')
  : t.substAll u (p::q::ps) allValid₁ allOrth₁ =
    t.substAll u (q::p::ps) allValid₂ allOrth₂ := by
  simp [substAll]
  congr 1
  apply substOrth'; grind

lemma substAllIdem {t : Term}
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
    . simp [h, substAll, substAtIdem]
    . intros
      have h' : p ⊥ hd := by grind
      rw [substAllSwap] <;> try grind
      . simp [substAll]
        apply ih <;> try grind
        . simp; constructor
          . apply orthValidL <;> grind
          . grind [substValidList]

lemma rewriteAtSubstAll {ℛ : Rules} {t : RTerm ℛ} {p : Position} {ru : Rule}
  (mem : ru ∈ ℛ)
  (mem' : p ∈ ps)
  (h : p.valid t)
  (isVar : p.get t h = var x)
  (allValid : ∀ p ∈ ps, p.valid t)
  (mtch : ∀ p' (mem : p' ∈ ps), ru.matchesAt t p' σ (allValid p' mem))
  (allOrth : ∀ p ∈ ps, ∀ q ∈ ps, p ≠ q → (p ⊥ q))
  : ru.rewriteAt t p σ h ~>*
  t.substAll (ru.rhs.apply σ) ps allValid allOrth := by
  sorry

-- Do I even need this one?
lemma rewriteAtVarIsSubst_aux {ℛ : Rules} {t : RTerm ℛ} {p : Position} {ru : Rule}
  (mem : ru ∈ ℛ)
  (h : p.valid t)
  (h' : p.valid (t.apply τ))
  (isVar : p.get t h = var x)
  (mtch : ru.matchesAt (t.apply τ) p σ h')
  (allValid : ∀ p ∈ varPos t x, p.valid (t.apply τ))
  (allOrth : ∀ p ∈ varPos t x, ∀ q ∈ varPos t x, p ≠ q → (p ⊥ q))
  : ru.rewriteAt (t.apply τ) p σ (validSubst _ _ τ h) ~>*
  (t.apply τ).substAll (ru.rhs.apply σ) (varPos t x) allValid allOrth := by sorry

lemma rewriteAtVarIsSubst {ℛ : Rules} {t : RTerm ℛ} {p : Position} {ru : Rule}
  (mem : ru ∈ ℛ)
  (h : p.valid t)
  (h' : p.get t h = var x)
  : ru.rewriteAt (t.apply τ) p σ (validSubst _ _ τ h) ~>*
    t.apply (varSubst x (ru.rhs.apply σ) |>.join τ) := by sorry

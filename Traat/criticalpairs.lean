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

end Position

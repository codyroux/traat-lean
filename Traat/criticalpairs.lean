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
  : p₁.valid t := by sorry

lemma validAppendTail {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : p₂.valid <| p₁.get t (validAppend h) := by sorry

lemma getAppend {p₁ p₂ : Position} (h : (p₁++p₂).valid t)
  : (p₁ ++ p₂).get t h = p₂.get (p₁.get t <| validAppend h) (validAppendTail h) := by sorry

end Position

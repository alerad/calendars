import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases

/-!
# Odù as Binary Vectors

An Odù is an element of {0,1}⁸, representing an 8-bit binary string.
This corresponds to two "legs" of 4 marks each in Ifá divination.

## Main definitions

* `Odu` : The type `Fin 8 → Fin 2` (256 elements)
* `complement` : Bitwise complement (flips all bits)
* `hammingDist` : Hamming distance between Odù

## Main results

* `complement_involutive` : comp(comp(o)) = o
* `hammingDist_complement` : d(o, comp(o)) = 8 (maximum possible)
* `hammingDist_le_eight` : d(o₁, o₂) ≤ 8 for all o₁, o₂
* `hammingDist_eq_eight_iff` : d(o₁, o₂) = 8 ↔ o₂ = comp(o₁)

## Semantic interpretation

The 16 base Odù are traditionally paired by complement:
- Ogbe (1111) ↔ Oyeku (0000) : Light ↔ Dark
- Iwori (0011) ↔ Odi (1100)
- etc.

This maximizes semantic distance (expansion ↔ contraction).
-/

namespace Ifa

abbrev Odu := Fin 8 → Fin 2

namespace Odu

theorem card : Fintype.card Odu = 256 := by native_decide

/-- Flip a single bit. -/
def flipBit (b : Fin 2) : Fin 2 := ⟨1 - b.val, by have := b.isLt; omega⟩

theorem flipBit_flipBit (b : Fin 2) : flipBit (flipBit b) = b := by
  simp only [flipBit]
  ext
  simp only [Fin.val_mk]
  have := b.isLt
  omega

theorem flipBit_ne (b : Fin 2) : flipBit b ≠ b := by
  simp only [flipBit, ne_eq]
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_mk] at hval
  have := b.isLt
  omega

/-- flipBit is the only other element of Fin 2. -/
theorem eq_or_eq_flipBit (a b : Fin 2) : a = b ∨ a = flipBit b := by
  fin_cases a <;> fin_cases b <;> simp [flipBit]

/-- If a ≠ b in Fin 2, then a = flipBit b. -/
theorem ne_implies_eq_flipBit (a b : Fin 2) (h : a ≠ b) : a = flipBit b := by
  cases eq_or_eq_flipBit a b with
  | inl heq => exact absurd heq h
  | inr hflip => exact hflip

/-- Bitwise complement (flips all 8 bits). -/
def complement (o : Odu) : Odu := fun i => flipBit (o i)

theorem complement_involutive : Function.Involutive complement := by
  intro o
  funext i
  simp only [complement]
  exact flipBit_flipBit (o i)

theorem complement_ne_self (o : Odu) : complement o ≠ o := by
  simp only [complement, ne_eq]
  intro h
  have h0 := congrFun h 0
  exact flipBit_ne (o 0) h0

/-- Hamming distance between two Odù. -/
def hammingDist (o₁ o₂ : Odu) : ℕ :=
  ((Finset.univ : Finset (Fin 8)).filter (fun i => o₁ i ≠ o₂ i)).card

theorem hammingDist_comm (o₁ o₂ : Odu) : hammingDist o₁ o₂ = hammingDist o₂ o₁ := by
  simp only [hammingDist]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

theorem hammingDist_self (o : Odu) : hammingDist o o = 0 := by
  simp only [hammingDist, ne_eq, not_true_eq_false, Finset.filter_False, Finset.card_empty]

/-- Upper bound: Hamming distance is at most 8. -/
theorem hammingDist_le_eight (o₁ o₂ : Odu) : hammingDist o₁ o₂ ≤ 8 := by
  simp only [hammingDist]
  calc ((Finset.univ : Finset (Fin 8)).filter (fun i => o₁ i ≠ o₂ i)).card
      ≤ (Finset.univ : Finset (Fin 8)).card := Finset.card_filter_le _ _
    _ = 8 := by rfl

/-- KEY THEOREM: Hamming distance to complement is exactly 8 (maximum). -/
theorem hammingDist_complement (o : Odu) : hammingDist o (complement o) = 8 := by
  simp only [hammingDist, ne_eq, complement]
  have heq : (Finset.univ : Finset (Fin 8)).filter (fun i => o i ≠ flipBit (o i)) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    constructor
    · intro _; trivial
    · intro _; exact (flipBit_ne (o i)).symm
  rw [heq, Finset.card_univ, Fintype.card_fin]

/-- If all bits differ, then o₂ = complement o₁. -/
theorem all_bits_differ_implies_complement (o₁ o₂ : Odu)
    (h : ∀ i : Fin 8, o₁ i ≠ o₂ i) : o₂ = complement o₁ := by
  funext i
  have hi := h i
  simp only [complement]
  exact ne_implies_eq_flipBit (o₂ i) (o₁ i) hi.symm

/-- If distance < 8, then there exists a bit that is equal. -/
theorem hammingDist_lt_eight_exists_eq (o₁ o₂ : Odu) (h : hammingDist o₁ o₂ < 8) :
    ∃ i : Fin 8, o₁ i = o₂ i := by
  simp only [hammingDist] at h
  by_contra hall
  push_neg at hall
  have : (Finset.univ : Finset (Fin 8)).filter (fun i => o₁ i ≠ o₂ i) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => hall i⟩
  rw [this, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- Complement is the ONLY element at distance 8 from any given Odù. -/
theorem hammingDist_eq_eight_iff (o₁ o₂ : Odu) :
    hammingDist o₁ o₂ = 8 ↔ o₂ = complement o₁ := by
  constructor
  · intro hdist
    -- If distance is 8, then no bit is equal
    have hall : ∀ i : Fin 8, o₁ i ≠ o₂ i := by
      intro i heq
      -- If some bit is equal, then distance < 8
      have hlt : hammingDist o₁ o₂ < 8 := by
        simp only [hammingDist]
        have hsub : (Finset.univ : Finset (Fin 8)).filter (fun j => o₁ j ≠ o₂ j) ⊂ Finset.univ := by
          constructor
          · intro x _; exact Finset.mem_univ x
          · intro hcontra
            have hi : i ∈ (Finset.univ : Finset (Fin 8)).filter (fun j => o₁ j ≠ o₂ j) :=
              hcontra (Finset.mem_univ i)
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hi
            exact hi heq
        have := Finset.card_lt_card hsub
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact this
      omega
    exact all_bits_differ_implies_complement o₁ o₂ hall
  · intro heq
    rw [heq]
    exact hammingDist_complement o₁

/-- An Odù is a Meji (doubled) if both legs are identical. -/
def isMeji (o : Odu) : Prop := o 0 = o 4 ∧ o 1 = o 5 ∧ o 2 = o 6 ∧ o 3 = o 7

instance : DecidablePred isMeji := fun o => by
  unfold isMeji
  infer_instance

/-- There are exactly 16 Meji forms (diagonal of the 16×16 matrix). -/
theorem meji_count : ((Finset.univ : Finset Odu).filter isMeji).card = 16 := by
  native_decide

end Odu

end Ifa

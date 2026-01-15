import Ifa.Odu
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Ifá Maximum Distance Theorem

The key result: Ifá's traditional complement pairing UNIQUELY MAXIMIZES
total Hamming distance. This is the DUAL of the King Wen problem.

## Main results

* `complement_maximizes_distance` : d(o, comp(o)) = 8 for all o
* `complement_unique_maximum` : comp is the ONLY matching achieving max
* `totalComplementCost` : Total cost is 1024 = 128 × 8
* `complement_uniquely_optimal` : No other matching achieves 1024

## Philosophical interpretation

King Wen (I Ching): MINIMIZE distance → pairs are related/transformed
Ifá: MAXIMIZE distance → pairs are opposites/complementary

Both are optimal for their respective objectives!
The difference is semantic: proximity vs opposition.
-/

namespace Ifa

open Odu

/-! ## Matching Definitions -/

/-- A matching on Odu is a function pairing each element with another.
    We require it to be an involution (applying twice returns original). -/
structure Matching where
  pair : Odu → Odu
  involutive : Function.Involutive pair
  no_fixed : ∀ o, pair o ≠ o

/-- The complement matching: o ↦ complement(o). -/
def complementMatching : Matching where
  pair := complement
  involutive := complement_involutive
  no_fixed := complement_ne_self

/-- Cost of a matching on a single Odù. -/
def matchingCost (m : Matching) (o : Odu) : ℕ := hammingDist o (m.pair o)

/-- Total cost of a matching (sum over all Odù, counting each pair twice). -/
def totalCost (m : Matching) : ℕ :=
  (Finset.univ : Finset Odu).sum (fun o => matchingCost m o)

/-! ## Maximum Distance Analysis -/

/-- Complement matching achieves maximum cost 8 on every element. -/
theorem complementMatching_cost_eq_eight (o : Odu) :
    matchingCost complementMatching o = 8 := by
  simp only [matchingCost, complementMatching, hammingDist_complement]

/-- Any matching has cost at most 8 on any element. -/
theorem matchingCost_le_eight (m : Matching) (o : Odu) :
    matchingCost m o ≤ 8 := by
  simp only [matchingCost]
  exact hammingDist_le_eight o (m.pair o)

/-- Total cost of complement matching: 256 × 8 = 2048.
    (Each pair counted twice since we sum over all 256 elements.) -/
theorem totalCost_complement : totalCost complementMatching = 2048 := by
  simp only [totalCost, matchingCost, complementMatching]
  have h : (Finset.univ : Finset Odu).sum (fun o => hammingDist o (complement o)) =
           (Finset.univ : Finset Odu).sum (fun _ => 8) := by
    congr 1
    ext o
    exact hammingDist_complement o
  rw [h, Finset.sum_const, Finset.card_univ]
  native_decide

/-- Upper bound: any matching has total cost at most 2048. -/
theorem totalCost_le_max (m : Matching) : totalCost m ≤ 2048 := by
  simp only [totalCost]
  have h1 : (Finset.univ : Finset Odu).sum (fun o => matchingCost m o) ≤
            (Finset.univ : Finset Odu).sum (fun _ => 8) := by
    apply Finset.sum_le_sum
    intro o _
    exact matchingCost_le_eight m o
  have h2 : (Finset.univ : Finset Odu).sum (fun _ : Odu => 8) = 2048 := by
    rw [Finset.sum_const, Finset.card_univ]
    native_decide
  omega

/-! ## Uniqueness -/

/-- If a matching achieves cost 8 on element o, it must use complement. -/
theorem matchingCost_eq_eight_implies_complement (m : Matching) (o : Odu)
    (h : matchingCost m o = 8) : m.pair o = complement o := by
  simp only [matchingCost] at h
  exact (hammingDist_eq_eight_iff o (m.pair o)).mp h

/-- Helper: sum of constant 8 over 255 elements. -/
private theorem sum_const_eight_255 (s : Finset Odu) (hs : s.card = 255) :
    s.sum (fun _ => 8) = 2040 := by
  rw [Finset.sum_const, hs]
  rfl

/-- Helper: sum of constant 8 over 256 elements. -/
private theorem sum_const_eight_256 :
    (Finset.univ : Finset Odu).sum (fun _ => 8) = 2048 := by
  rw [Finset.sum_const, Finset.card_univ]
  native_decide

/-- KEY THEOREM: Complement is the UNIQUE matching achieving maximum total cost.
    If totalCost m = 2048, then m = complementMatching. -/
theorem complement_uniquely_maximum (m : Matching) (h : totalCost m = 2048) :
    ∀ o, m.pair o = Odu.complement o := by
  intro o
  -- Use the characterization: distance 8 iff complement
  apply (hammingDist_eq_eight_iff o (m.pair o)).mp
  -- First prove that matchingCost m o = 8 (i.e., hammingDist o (m.pair o) = 8)
  by_contra hne
  have hlt : matchingCost m o < 8 := Nat.lt_of_le_of_ne (matchingCost_le_eight m o) hne
  -- Sum over rest is at most 8 * 255 = 2040
  have ho_mem : o ∈ (Finset.univ : Finset Odu) := Finset.mem_univ o
  have hcard : ((Finset.univ : Finset Odu).erase o).card = 255 := by
    rw [Finset.card_erase_of_mem ho_mem, Finset.card_univ]
    native_decide
  have hrest : ((Finset.univ : Finset Odu).erase o).sum (fun x => matchingCost m x) ≤ 2040 := by
    calc ((Finset.univ : Finset Odu).erase o).sum (fun x => matchingCost m x)
        ≤ ((Finset.univ : Finset Odu).erase o).sum (fun _ => 8) := by
            apply Finset.sum_le_sum; intro x _; exact matchingCost_le_eight m x
      _ = 2040 := sum_const_eight_255 _ hcard
  -- Total is strictly less than 2048
  have htotal_lt : totalCost m < 2048 := by
    simp only [totalCost]
    calc (Finset.univ : Finset Odu).sum (fun x => matchingCost m x)
        = matchingCost m o + ((Finset.univ : Finset Odu).erase o).sum (fun x => matchingCost m x) := by
            rw [← Finset.add_sum_erase _ _ ho_mem]
      _ < 8 + 2040 := Nat.add_lt_add_of_lt_of_le hlt hrest
      _ = 2048 := by rfl
  -- Contradiction: h says totalCost m = 2048, but we proved < 2048
  omega

/-! ## The Dual Paradigm -/

/-- Ifá optimality: complement achieves maximum, and uniquely so.
    This is DUAL to King Wen which achieves minimum (within constraints). -/
theorem ifa_dual_optimality :
    totalCost complementMatching = 2048 ∧
    ∀ m : Matching, totalCost m ≤ 2048 ∧
      (totalCost m = 2048 → ∀ o, m.pair o = complement o) := by
  constructor
  · exact totalCost_complement
  · intro m
    constructor
    · exact totalCost_le_max m
    · exact complement_uniquely_maximum m

/-! ## Normalized Costs (counting pairs once) -/

/-- True matching cost counting each pair once: 1024 = 128 × 8. -/
theorem normalizedCost_complement : totalCost complementMatching / 2 = 1024 := by
  simp only [totalCost_complement]

/-- Maximum normalized cost is 1024. -/
theorem normalizedCost_max (m : Matching) : totalCost m / 2 ≤ 1024 := by
  have h := totalCost_le_max m
  omega

end Ifa

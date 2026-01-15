import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic

/-!
# Calendar Round as Z₁₈₉₈₀

The Mesoamerican Calendar Round combines:
- Tzolkin (260 days) = Z₁₃ × Z₂₀ = Z₁₃ × Z₄ × Z₅
- Haab (365 days) = Z₇₃ × Z₅

The key insight: GCD(260, 365) = 5

This means the Calendar Round decomposes as:
  Z₁₈₉₈₀ ≅ Z₄ × Z₅ × Z₁₃ × Z₇₃

where Z₅ is SHARED between Tzolkin and Haab!

## Main results

* `cr_card` : |CalendarRound| = 18980
* `gcd_260_365` : GCD(260, 365) = 5
* `z5_shared` : The Z₅ component is determined by both Tzolkin and Haab
-/

namespace CalendarRound

/-! ## Basic Definitions -/

/-- The Calendar Round as Z₁₈₉₈₀. -/
abbrev Day := Fin 18980

/-- Component type abbreviations. -/
abbrev Z4 := Fin 4
abbrev Z5 := Fin 5
abbrev Z13 := Fin 13
abbrev Z73 := Fin 73

/-- The Calendar Round has 18980 days. -/
theorem cr_card : Fintype.card Day = 18980 := by native_decide

/-- 18980 = 52 × 365 = 73 × 260. -/
theorem cr_factorization : 18980 = 52 * 365 ∧ 18980 = 73 * 260 := by omega

/-! ## Number Theory -/

/-- GCD(260, 365) = 5. -/
theorem gcd_260_365 : Nat.gcd 260 365 = 5 := by native_decide

/-- LCM(260, 365) = 18980. -/
theorem lcm_260_365 : Nat.lcm 260 365 = 18980 := by native_decide

/-- Prime factorizations. -/
theorem factorization_260 : 260 = 4 * 5 * 13 := by omega
theorem factorization_365 : 365 = 5 * 73 := by omega
theorem factorization_18980 : 18980 = 4 * 5 * 13 * 73 := by omega

/-! ## Component Projections -/

/-- Project to Z₄ component. -/
def toZ4 (d : Day) : Z4 := ⟨d.val % 4, Nat.mod_lt _ (by omega)⟩

/-- Project to Z₅ component. -/
def toZ5 (d : Day) : Z5 := ⟨d.val % 5, Nat.mod_lt _ (by omega)⟩

/-- Project to Z₁₃ component. -/
def toZ13 (d : Day) : Z13 := ⟨d.val % 13, Nat.mod_lt _ (by omega)⟩

/-- Project to Z₇₃ component. -/
def toZ73 (d : Day) : Z73 := ⟨d.val % 73, Nat.mod_lt _ (by omega)⟩

/-! ## Tzolkin and Haab Views -/

/-- Tzolkin position (d mod 260). -/
def tzolkinPos (d : Day) : Fin 260 := ⟨d.val % 260, Nat.mod_lt _ (by omega)⟩

/-- Haab position (d mod 365). -/
def haabPos (d : Day) : Fin 365 := ⟨d.val % 365, Nat.mod_lt _ (by omega)⟩

/-- The Z₅ component from Tzolkin. -/
def tzolkinZ5 (d : Day) : Z5 := ⟨(tzolkinPos d).val % 5, Nat.mod_lt _ (by omega)⟩

/-- The Z₅ component from Haab. -/
def haabZ5 (d : Day) : Z5 := ⟨(haabPos d).val % 5, Nat.mod_lt _ (by omega)⟩

/-- KEY THEOREM: Z₅ is shared between Tzolkin and Haab! -/
theorem z5_shared : ∀ d : Day, tzolkinZ5 d = haabZ5 d := by
  intro d
  simp only [tzolkinZ5, haabZ5, tzolkinPos, haabPos]
  congr 1
  have h : d.val % 260 % 5 = d.val % 5 := Nat.mod_mod_of_dvd d.val (by omega : 5 ∣ 260)
  have h' : d.val % 365 % 5 = d.val % 5 := Nat.mod_mod_of_dvd d.val (by omega : 5 ∣ 365)
  omega

/-- Both equal the global Z₅ component. -/
theorem z5_global : ∀ d : Day, tzolkinZ5 d = toZ5 d ∧ haabZ5 d = toZ5 d := by
  intro d
  constructor
  · simp only [tzolkinZ5, toZ5, tzolkinPos]
    congr 1
    exact Nat.mod_mod_of_dvd d.val (by omega : 5 ∣ 260)
  · simp only [haabZ5, toZ5, haabPos]
    congr 1
    exact Nat.mod_mod_of_dvd d.val (by omega : 5 ∣ 365)

/-! ## Circular Distance -/

/-- Circular distance on Fin n. -/
def circDist {n : ℕ} [NeZero n] (a b : Fin n) : ℕ :=
  let d := if a.val ≤ b.val then b.val - a.val else a.val - b.val
  min d (n - d)

theorem circDist_comm {n : ℕ} [NeZero n] (a b : Fin n) : circDist a b = circDist b a := by
  simp only [circDist]
  split_ifs with h1 h2 h2 <;> omega

theorem circDist_self {n : ℕ} [NeZero n] (a : Fin n) : circDist a a = 0 := by
  simp only [circDist, le_refl, ↓reduceIte, Nat.sub_self, ge_iff_le, Nat.zero_min]

/-- Calendar Round product metric (sum of circular distances on each CRT factor).
    NOTE: This is NOT the native circular distance d₁₈₉₈₀ on Z₁₈₉₈₀.
    The CRT is a group isomorphism, not an isometry. -/
def crDist (d1 d2 : Day) : ℕ :=
  circDist (toZ4 d1) (toZ4 d2) +
  circDist (toZ5 d1) (toZ5 d2) +
  circDist (toZ13 d1) (toZ13 d2) +
  circDist (toZ73 d1) (toZ73 d2)

theorem crDist_comm (d1 d2 : Day) : crDist d1 d2 = crDist d2 d1 := by
  simp only [crDist, circDist_comm]

theorem crDist_self (d : Day) : crDist d d = 0 := by
  simp only [crDist, circDist_self, add_zero]

/-! ## Z₅ Classes -/

/-- Days in a Z₅ class. -/
def z5Class (k : Z5) : Finset Day :=
  Finset.univ.filter (fun d => toZ5 d = k)

/-- Each Z₅ class has 3796 days. -/
theorem z5Class_card : ∀ k : Z5, (z5Class k).card = 3796 := by native_decide

/-- 3796 = 18980 / 5. -/
theorem z5Class_size : 3796 = 18980 / 5 := by omega

end CalendarRound

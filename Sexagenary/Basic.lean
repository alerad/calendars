import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic

/-!
# Chinese Sexagenary Cycle as Z₆₀

The Chinese Sexagenary Cycle (干支 Gānzhī) combines:
- 10 Heavenly Stems (天干 Tiāngān) = Z₁₀ = Z₂ × Z₅
- 12 Earthly Branches (地支 Dìzhī) = Z₁₂ = Z₂ × Z₂ × Z₃

The key insight: GCD(10, 12) = 2

This means the Sexagenary Cycle decomposes as:
  Z₆₀ ≅ Z₂ × Z₅ × Z₂ × Z₃ = Z₂ × Z₅ × Z₆

where Z₂ is SHARED between Stems and Branches!

This Z₂ is exactly YIN/YANG (陰/陽):
- Yang stems (odd): 甲丙戊庚壬 (indices 0,2,4,6,8 when 1-indexed become 0,2,4,6,8)
- Yin stems (even): 乙丁己辛癸 (indices 1,3,5,7,9)
- Yang branches: 子寅辰午申戌 (Rat, Tiger, Dragon, Horse, Monkey, Dog)
- Yin branches: 丑卯巳未酉亥 (Ox, Rabbit, Snake, Goat, Rooster, Pig)

Pairing rule: Yang stems pair only with yang branches.
              Yin stems pair only with yin branches.

This is why only 60 combinations exist, not 120.

## Main results

* `sexagenary_card` : |SexagenaryCycle| = 60
* `gcd_10_12` : GCD(10, 12) = 2
* `z2_shared` : The Z₂ (yin/yang) component is determined by both Stem and Branch
-/

namespace Sexagenary

/-! ## Basic Definitions -/

/-- The Sexagenary Cycle as Z₆₀. -/
abbrev Year := Fin 60

/-- Component type abbreviations. -/
abbrev Z2 := Fin 2
abbrev Z3 := Fin 3
abbrev Z4 := Fin 4
abbrev Z5 := Fin 5

/-- The Heavenly Stems as Z₁₀. -/
abbrev Stem := Fin 10

/-- The Earthly Branches as Z₁₂. -/
abbrev Branch := Fin 12

/-- The Sexagenary Cycle has 60 years. -/
theorem sexagenary_card : Fintype.card Year = 60 := by native_decide

/-- 60 = 6 × 10 = 5 × 12. -/
theorem sexagenary_factorization : 60 = 6 * 10 ∧ 60 = 5 * 12 := by omega

/-! ## Number Theory -/

/-- GCD(10, 12) = 2. -/
theorem gcd_10_12 : Nat.gcd 10 12 = 2 := by native_decide

/-- LCM(10, 12) = 60. -/
theorem lcm_10_12 : Nat.lcm 10 12 = 60 := by native_decide

/-- Prime factorizations. -/
theorem factorization_10 : 10 = 2 * 5 := by omega
theorem factorization_12 : 12 = 2 * 2 * 3 := by omega
theorem factorization_60 : 60 = 2 * 2 * 3 * 5 := by omega

/-- Z₆₀ ≅ Z₅ × Z₁₂ ≅ Z₅ × Z₄ × Z₃ (sharing Z₂ within Z₄). -/
theorem factorization_crt : 60 = 5 * 12 ∧ 12 = 4 * 3 := by omega

/-! ## Component Projections -/

/-- Project to Z₂ (yin/yang) component. -/
def toZ2 (y : Year) : Z2 := ⟨y.val % 2, Nat.mod_lt _ (by omega)⟩

/-- Project to Z₃ component. -/
def toZ3 (y : Year) : Z3 := ⟨y.val % 3, Nat.mod_lt _ (by omega)⟩

/-- Project to Z₅ component. -/
def toZ5 (y : Year) : Z5 := ⟨y.val % 5, Nat.mod_lt _ (by omega)⟩

/-- Project to Z₄ component (contains Z₂). -/
def toZ4 (y : Year) : Z4 := ⟨y.val % 4, Nat.mod_lt _ (by omega)⟩

/-! ## Stem and Branch Views -/

/-- Heavenly Stem (y mod 10). -/
def toStem (y : Year) : Stem := ⟨y.val % 10, Nat.mod_lt _ (by omega)⟩

/-- Earthly Branch (y mod 12). -/
def toBranch (y : Year) : Branch := ⟨y.val % 12, Nat.mod_lt _ (by omega)⟩

/-- The Z₂ (yin/yang) component from Stem. -/
def stemZ2 (y : Year) : Z2 := ⟨(toStem y).val % 2, Nat.mod_lt _ (by omega)⟩

/-- The Z₂ (yin/yang) component from Branch. -/
def branchZ2 (y : Year) : Z2 := ⟨(toBranch y).val % 2, Nat.mod_lt _ (by omega)⟩

/-- KEY THEOREM: Z₂ (yin/yang) is shared between Stem and Branch! -/
theorem z2_shared : ∀ y : Year, stemZ2 y = branchZ2 y := by
  intro y
  simp only [stemZ2, branchZ2, toStem, toBranch]
  congr 1
  have h : y.val % 10 % 2 = y.val % 2 := Nat.mod_mod_of_dvd y.val (by omega : 2 ∣ 10)
  have h' : y.val % 12 % 2 = y.val % 2 := Nat.mod_mod_of_dvd y.val (by omega : 2 ∣ 12)
  omega

/-- Both equal the global Z₂ component. -/
theorem z2_global : ∀ y : Year, stemZ2 y = toZ2 y ∧ branchZ2 y = toZ2 y := by
  intro y
  constructor
  · simp only [stemZ2, toZ2, toStem]
    congr 1
    exact Nat.mod_mod_of_dvd y.val (by omega : 2 ∣ 10)
  · simp only [branchZ2, toZ2, toBranch]
    congr 1
    exact Nat.mod_mod_of_dvd y.val (by omega : 2 ∣ 12)

/-! ## Yin/Yang Classification -/

/-- A year is Yang if its Z₂ component is 0. -/
def isYang (y : Year) : Bool := toZ2 y = 0

/-- A year is Yin if its Z₂ component is 1. -/
def isYin (y : Year) : Bool := toZ2 y = 1

/-- Year 0 (甲子 Jiǎzǐ) is Yang. -/
theorem year0_yang : isYang ⟨0, by omega⟩ = true := by native_decide

/-- Year 1 (乙丑 Yǐchǒu) is Yin. -/
theorem year1_yin : isYin ⟨1, by omega⟩ = true := by native_decide

/-- 30 Yang years. -/
theorem yang_count : (Finset.univ.filter (fun y : Year => isYang y)).card = 30 := by native_decide

/-- 30 Yin years. -/
theorem yin_count : (Finset.univ.filter (fun y : Year => isYin y)).card = 30 := by native_decide

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

/-- Sexagenary product metric (sum of circular distances on each CRT factor).
    Uses Z₅ × Z₄ × Z₃ decomposition (where Z₂ ⊂ Z₄ is locked).
    NOTE: This is NOT the native circular distance d₆₀ on Z₆₀.
    The CRT is a group isomorphism, not an isometry.
    E.g., sexDist 1 2 = 3 but d₆₀(1,2) = 1. -/
def sexDist (y1 y2 : Year) : ℕ :=
  circDist (toZ5 y1) (toZ5 y2) +
  circDist (toZ4 y1) (toZ4 y2) +
  circDist (toZ3 y1) (toZ3 y2)

theorem sexDist_comm (y1 y2 : Year) : sexDist y1 y2 = sexDist y2 y1 := by
  simp only [sexDist, circDist_comm]

theorem sexDist_self (y : Year) : sexDist y y = 0 := by
  simp only [sexDist, circDist_self, add_zero]

/-! ## Z₂ Classes (Yin/Yang) -/

/-- Years in a Z₂ class. -/
def z2Class (k : Z2) : Finset Year :=
  Finset.univ.filter (fun y => toZ2 y = k)

/-- Each Z₂ class has 30 years. -/
theorem z2Class_card : ∀ k : Z2, (z2Class k).card = 30 := by native_decide

/-- 30 = 60 / 2. -/
theorem z2Class_size : 30 = 60 / 2 := by omega

/-! ## The 10 Heavenly Stems -/

/-- Stem names (Pinyin). -/
def stemName : Stem → String
  | ⟨0, _⟩ => "甲 Jiǎ"
  | ⟨1, _⟩ => "乙 Yǐ"
  | ⟨2, _⟩ => "丙 Bǐng"
  | ⟨3, _⟩ => "丁 Dīng"
  | ⟨4, _⟩ => "戊 Wù"
  | ⟨5, _⟩ => "己 Jǐ"
  | ⟨6, _⟩ => "庚 Gēng"
  | ⟨7, _⟩ => "辛 Xīn"
  | ⟨8, _⟩ => "壬 Rén"
  | ⟨9, _⟩ => "癸 Guǐ"

/-! ## The 12 Earthly Branches -/

/-- Branch names (Pinyin) with animals. -/
def branchName : Branch → String
  | ⟨0, _⟩ => "子 Zǐ (Rat)"
  | ⟨1, _⟩ => "丑 Chǒu (Ox)"
  | ⟨2, _⟩ => "寅 Yín (Tiger)"
  | ⟨3, _⟩ => "卯 Mǎo (Rabbit)"
  | ⟨4, _⟩ => "辰 Chén (Dragon)"
  | ⟨5, _⟩ => "巳 Sì (Snake)"
  | ⟨6, _⟩ => "午 Wǔ (Horse)"
  | ⟨7, _⟩ => "未 Wèi (Goat)"
  | ⟨8, _⟩ => "申 Shēn (Monkey)"
  | ⟨9, _⟩ => "酉 Yǒu (Rooster)"
  | ⟨10, _⟩ => "戌 Xū (Dog)"
  | ⟨11, _⟩ => "亥 Hài (Pig)"

end Sexagenary

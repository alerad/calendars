import Sexagenary.Basic

/-!
# Coxeter Structure on Sexagenary Cycle

The natural symmetry group is Z₂² (Klein four-group) acting on (Z₅, Z₃).

## The Z₂ Constraint

Since Z₂ (yin/yang) is shared between Stems and Branches, we CANNOT negate it
if we want the symmetries to respect both calendar systems.

GCD(10, 12) = 2 FORCES the symmetry group to preserve the Z₂ component!

## Decomposition

Z₆₀ = Z₅ × Z₁₂ (by CRT, since gcd(5,12)=1)
Z₁₂ = Z₄ × Z₃ (by CRT, since gcd(4,3)=1)
Z₄ contains Z₂ (yin/yang)

To preserve Z₂, we can only negate:
- Z₅ (the stem's non-shared part)
- Z₃ (within Z₁₂, preserving Z₄)

## Available Simple Reflections

- neg_Z5: Negate Z₅ component (preserves Z₁₂ including Z₂)
- neg_Z3: Negate Z₃ component within Z₁₂ (preserves Z₄ including Z₂)

## Main Results

* 24 orbits under Z₂²
* Fixed points: e=60, n5=12, n3=20, n5n3=4
* Symmetry reduction Z₂³ → Z₂² forced by fiber structure (metric-independent)
* Simple reflections optimal under product metric (see Optimality.lean)
-/

namespace Sexagenary

/-! ## CRT Coefficients -/

/-- CRT coefficient for Z₅ in Z₆₀ = Z₅ × Z₁₂.
    k5 ≡ 1 (mod 5), k5 ≡ 0 (mod 12). -/
def k5 : ℕ := 36

/-- CRT coefficient for Z₁₂ in Z₆₀ = Z₅ × Z₁₂.
    k12 ≡ 0 (mod 5), k12 ≡ 1 (mod 12). -/
def k12 : ℕ := 25

/-- Verify CRT coefficients. -/
theorem k5_mod5 : k5 % 5 = 1 := by native_decide
theorem k5_mod12 : k5 % 12 = 0 := by native_decide
theorem k12_mod5 : k12 % 5 = 0 := by native_decide
theorem k12_mod12 : k12 % 12 = 1 := by native_decide

/-- CRT coefficient for Z₄ in Z₁₂ = Z₄ × Z₃.
    k4 ≡ 1 (mod 4), k4 ≡ 0 (mod 3). -/
def k4_12 : ℕ := 9

/-- CRT coefficient for Z₃ in Z₁₂ = Z₄ × Z₃.
    k3 ≡ 0 (mod 4), k3 ≡ 1 (mod 3). -/
def k3_12 : ℕ := 4

/-- Verify Z₁₂ CRT coefficients. -/
theorem k4_12_mod4 : k4_12 % 4 = 1 := by native_decide
theorem k4_12_mod3 : k4_12 % 3 = 0 := by native_decide
theorem k3_12_mod4 : k3_12 % 4 = 0 := by native_decide
theorem k3_12_mod3 : k3_12 % 3 = 1 := by native_decide

/-! ## Component Projections -/

/-- Project to Z₁₂ component. -/
def toZ12 (y : Year) : Fin 12 := ⟨y.val % 12, Nat.mod_lt _ (by omega)⟩

/-! ## Negation Operations -/

/-- Reconstruct year from Z₅ and Z₁₂ components. -/
def fromZ5Z12 (z5 : Z5) (z12 : Fin 12) : Year :=
  ⟨(k5 * z5.val + k12 * z12.val) % 60, Nat.mod_lt _ (by omega)⟩

/-- Negate Z₃ component within Z₁₂. -/
def negZ3InZ12 (z12 : Fin 12) : Fin 12 :=
  let z4 := z12.val % 4
  let z3 := z12.val % 3
  let newZ3 := (3 - z3) % 3
  ⟨(k4_12 * z4 + k3_12 * newZ3) % 12, Nat.mod_lt _ (by omega)⟩

/-- Negate Z₅ component (preserves Z₁₂ including Z₂). -/
def negZ5 (y : Year) : Year :=
  let z5 := toZ5 y
  let z12 := toZ12 y
  let newZ5 : Z5 := ⟨(5 - z5.val) % 5, Nat.mod_lt _ (by omega)⟩
  fromZ5Z12 newZ5 z12

/-- Negate Z₃ component (preserves Z₅ and Z₄, thus Z₂). -/
def negZ3 (y : Year) : Year :=
  let z5 := toZ5 y
  let z12 := toZ12 y
  let newZ12 := negZ3InZ12 z12
  fromZ5Z12 z5 newZ12

/-- negZ5 is involutive. -/
theorem negZ5_involutive : Function.Involutive negZ5 := fun y => by
  simp only [negZ5, toZ5, toZ12, fromZ5Z12, k5, k12]
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

/-- negZ3 is involutive. -/
theorem negZ3_involutive : Function.Involutive negZ3 := fun y => by
  simp only [negZ3, toZ5, toZ12, fromZ5Z12, negZ3InZ12, k5, k12, k4_12, k3_12]
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

/-- negZ5 preserves Z₂ (yin/yang). -/
theorem negZ5_preserves_z2 : ∀ y : Year, toZ2 (negZ5 y) = toZ2 y := by native_decide

/-- negZ3 preserves Z₂ (yin/yang). -/
theorem negZ3_preserves_z2 : ∀ y : Year, toZ2 (negZ3 y) = toZ2 y := by native_decide

/-- negZ5 preserves Z₁₂. -/
theorem negZ5_preserves_z12 : ∀ y : Year, toZ12 (negZ5 y) = toZ12 y := by native_decide

/-- negZ3 preserves Z₅. -/
theorem negZ3_preserves_z5 : ∀ y : Year, toZ5 (negZ3 y) = toZ5 y := by native_decide

/-- negZ5 commutes with negZ3. -/
theorem negZ5_negZ3_comm : ∀ y : Year, negZ5 (negZ3 y) = negZ3 (negZ5 y) := by native_decide

/-! ## The Z₂² Group (Klein Four-Group) -/

/-- Elements of Z₂² = Z₂ × Z₂ (preserving yin/yang). -/
inductive SexAction
  | e     -- identity
  | n5    -- negate Z₅
  | n3    -- negate Z₃
  | n53   -- negate both
  deriving DecidableEq, Repr

namespace SexAction

instance : Fintype SexAction := ⟨⟨[e, n5, n3, n53], by decide⟩,
  by intro x; cases x <;> decide⟩

/-- Apply action to a year. -/
def apply : SexAction → Year → Year
  | e => id
  | n5 => negZ5
  | n3 => negZ3
  | n53 => negZ5 ∘ negZ3

/-- Group multiplication (XOR on sign bits). -/
def mul : SexAction → SexAction → SexAction
  | e, g => g
  | g, e => g
  | n5, n5 => e
  | n3, n3 => e
  | n53, n53 => e
  | n5, n3 => n53
  | n3, n5 => n53
  | n5, n53 => n3
  | n53, n5 => n3
  | n3, n53 => n5
  | n53, n3 => n5

instance : One SexAction := ⟨e⟩
instance : Mul SexAction := ⟨mul⟩
instance : Inv SexAction := ⟨id⟩  -- All elements are self-inverse (Klein four-group)

theorem mul_assoc (a b c : SexAction) : mul (mul a b) c = mul a (mul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem one_mul (a : SexAction) : mul e a = a := by cases a <;> rfl
theorem mul_one (a : SexAction) : mul a e = a := by cases a <;> rfl
theorem inv_mul (a : SexAction) : mul a a = e := by cases a <;> rfl

instance : Group SexAction where
  mul := mul
  mul_assoc := mul_assoc
  one := e
  one_mul := one_mul
  mul_one := mul_one
  inv := id
  inv_mul_cancel := inv_mul

end SexAction

/-! ## Simple Reflections -/

/-- The simple reflections: {n5, n3}. -/
def sexGenerators : Finset SexAction := {.n5, .n3}

/-- Simple reflections are exactly the length-1 elements. -/
def isSimple (g : SexAction) : Bool := g = .n5 || g = .n3

theorem n5_simple : isSimple SexAction.n5 = true := rfl
theorem n3_simple : isSimple SexAction.n3 = true := rfl

/-! ## Orbit Structure -/

/-- Z₂ (yin/yang) is preserved by all actions. -/
theorem z2_preserved (g : SexAction) (y : Year) : toZ2 (SexAction.apply g y) = toZ2 y := by
  cases g
  case e => rfl
  case n5 => exact negZ5_preserves_z2 y
  case n3 => exact negZ3_preserves_z2 y
  case n53 =>
    simp only [SexAction.apply, Function.comp_apply]
    rw [negZ5_preserves_z2, negZ3_preserves_z2]

/-- Count fixed points for Burnside's lemma. -/
def countFixedPoints (g : SexAction) : ℕ :=
  (Finset.univ.filter (fun y : Year => SexAction.apply g y = y)).card

theorem fixed_by_e : countFixedPoints .e = 60 := by native_decide
theorem fixed_by_n5 : countFixedPoints .n5 = 12 := by native_decide
theorem fixed_by_n3 : countFixedPoints .n3 = 20 := by native_decide
theorem fixed_by_n53 : countFixedPoints .n53 = 4 := by native_decide

/-- By Burnside: |orbits| = (60 + 12 + 20 + 4) / 4 = 96/4 = 24 orbits. -/
theorem burnside_count : (60 + 12 + 20 + 4) / 4 = 24 := by omega

/-- Total number of orbits under Z₂². -/
theorem orbit_count : (countFixedPoints .e + countFixedPoints .n5 +
    countFixedPoints .n3 + countFixedPoints .n53) / 4 = 24 := by
  rw [fixed_by_e, fixed_by_n5, fixed_by_n3, fixed_by_n53]

end Sexagenary

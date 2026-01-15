Once is chance.
 Twice is coincidence.
 Three times is structure.

# Fiber Product Structure in Cyclic Calendar Systems

Lean 4 formalization of structural and metric results across five calendar/divination systems.

## Structure (metric-independent)

- **Fiber products**: Z₁₈₉₈₀ ≅ Z₂₆₀ ×_{Z₅} Z₃₆₅ (Calendar Round), Z₆₀ ≅ Z₁₀ ×_{Z₂} Z₁₂ (Sexagenary)
- **Shared components**: Z₅ (Tzolkin/Haab), Z₂ yin/yang (Stems/Branches)
- **Symmetry reduction**: Z₂⁴ → Z₂³ (Calendar Round), Z₂³ → Z₂² (Sexagenary) — forced by fiber structure
- **Orbit counts**: 3885 (Calendar Round), 24 (Sexagenary) — via Burnside's lemma

## Optimality (under product metric)

Under the product metric (ℓ¹ on CRT factors), simple coordinate reflections always achieve optimal pairing cost. This follows from cost additivity (generators have disjoint supports) and min ≤ sum.

**Important**: The product metric on a CRT decomposition is NOT the native circular metric. The CRT is a group isomorphism, not an isometry. E.g., d₅ + d₄ + d₃ evaluated at (1,2) gives 3, but d₆₀(1,2) = 1.

## Boolean hypercube systems (Hamming metric)

- **I Ching** ({0,1}⁶): Complement + reversal act on ALL bits, so cost additivity fails and composites CAN win.
- **Ifá** ({0,1}⁴): Complement uniquely maximizes Hamming distance.

## Files

| Module | Contents |
|---|---|
| `CalendarRound/` | Basic defs, Coxeter group, optimality, fiber bundle |
| `Sexagenary/` | Basic defs, Coxeter group, optimality, fiber bundle |
| `Ifa/` | Odù encoding, Hamming-metric optimality |
| `MetaTheorem.lean` | Abstract product-metric optimality theorem |
| `paper_calendars.tex` | Companion paper |

## Building

```
lake build
```

Requires Lean 4 + Mathlib v4.20.0.

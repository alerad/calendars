import Lake
open Lake DSL

package Calendars where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.20.0"

@[default_target]
lean_lib CalendarRound where
  globs := #[.submodules `CalendarRound]

@[default_target]
lean_lib Sexagenary where
  globs := #[.submodules `Sexagenary]

@[default_target]
lean_lib Ifa where
  globs := #[.submodules `Ifa]

@[default_target]
lean_lib MetaTheorem where

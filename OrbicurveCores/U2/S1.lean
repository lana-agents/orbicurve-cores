/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.U2.Statement
import OrbicurveCores.S1.Main

/-!
# The S1 input of U2

`S1NonExceptional` holds by S1 (`S1.not_takeuchi_of_nonExceptional`).
-/

namespace OrbicurveCores

theorem s1NonExceptional : S1NonExceptional :=
  fun W _ A B hU hj ↦ S1.not_takeuchi_of_nonExceptional W A B hU hj

end OrbicurveCores

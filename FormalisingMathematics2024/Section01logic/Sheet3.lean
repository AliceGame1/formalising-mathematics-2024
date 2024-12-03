/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro hNT
  change True → False at hNT
  apply hNT
  triv
  done

example : False → ¬True := by
  intro hF
  change True → False
  intro hTF
  exact hF
  done

example : ¬False → True := by
  intro hnF
  by_contra hF
  change True → False at hF
  apply hF
  triv
  done

example : True → ¬False := by
  intro hT
  by_contra hF
  exact hF
  done

example : False → ¬P := by
  intro hF
  by_contra hP
  exact hF
  done

example : P → ¬P → False := by
  intro hP
  intro hnP
  change P → False at hnP
  apply hnP at hP
  exact hP
  done

example : P → ¬¬P := by
  intro hP
  change ¬P → False
  by_contra hnP
  change P → False at hnP
  apply hnP at hP
  exact hP
  done

example : (P → Q) → ¬Q → ¬P := by
  sorry
  done

example : ¬¬False → False := by
  intro h
  change ¬False → False at h
  by_contra hnF
  apply h at hnF
  exact hnF
  done

example : ¬¬P → P := by
  sorry
  done

example : (¬Q → ¬P) → P → Q := by
  sorry
  done

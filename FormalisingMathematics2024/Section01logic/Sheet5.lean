/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro hPQ
  rw [hPQ]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro hPQ
  rw [hPQ]
  intro hQP
  rw [hQP]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPQ
  rw [hPQ]
  intro hQR
  rw [hQR]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro hPaQ
  constructor
  cases' hPaQ with hP hQ
  exact hQ
  cases' hPaQ with hP hQ
  exact hP
  intro hQaP
  constructor
  cases' hQaP with hQ hP
  exact hP
  cases' hQaP with hQ hP
  exact hQ
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro hPaQaR
    cases' hPaQaR with hPaQ hR
    cases' hPaQ with hP hQ
    constructor
    · exact hP
    · constructor
      · exact hQ
      · exact hR
  · rintro ⟨hP, hQ, hR⟩
    exact ⟨⟨hP, hQ⟩, hR⟩
  done

example : P ↔ P ∧ True := by
  constructor
  · intro hP
    constructor
    exact hP
    triv
  · intro hPaT
    cases' hPaT with hP hT
    exact hP
  done

example : False ↔ P ∧ False := by
  sorry
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry
  done

example : ¬(P ↔ ¬P) := by
  change (P ↔ ¬P) → False
  intro hPnP
  cases' hPnP with hPnP hnPP
  have hnP : ¬P := by
    intro hnP
    apply hPnP at hnP
    apply hPnP
    apply hnPP at hnP
    exact hnP
    apply hnPP at hnP
    exact hnP
  apply hnP
  apply hnPP
  exact hnP
  done

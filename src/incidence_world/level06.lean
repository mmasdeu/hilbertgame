import tutorial_world.incidenceplane --hide
import incidence_world.level05 --hide
open IncidencePlane --hide

/-
Using the lemma we have just proved, we can now prove the following theorem.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Theorem :
Given a point `P`, there are at least two different lines that pass through it.
-/
theorem point_exists_two_lines {P : Ω} : ∃ (r l: Line Ω), P ∈ l ∧ P ∈ r ∧ l ≠ r :=
begin
  rcases (point_existnce_postulate P) with ⟨Q, R, ⟨hPQ, hPR, hQR,H⟩⟩,
  use line_through P Q, use line_through P R,
  repeat { split },
  {
    exact line_through_left P R,
  },
  {
    exact line_through_left P Q,
  },
  {
    exact if_pont_in_line_and_not_in_other_diferent (line_through_right P R) H,
  }
  
  
  
  
end
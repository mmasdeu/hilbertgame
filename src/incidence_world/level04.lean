import tutorial_world.incidenceplane --hide
import .level03 --hide
open IncidencePlane --hide

/-
Using the lemma specified before, we are going to prove the next incidence theorem.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Theorem :
Given a point `P`, there exist two points `Q` and `R`, such that the three points are collinear.
-/
theorem point_existnce_postulate (P : Ω) : ∃ (Q R : Ω), P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ 
¬ R ∈ (line_through P Q) :=
begin
  rcases (@existence Ω _) with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  by_cases hA : P = A,
  {
    rw hA,
    use B, use C,
    exact ⟨hAB, hAC, hBC, h⟩,
  },
  {
    have := exist_point_not_in_line (line_through' P A),
    cases this with D hD,
    use A, use D,
    have hPD := point_in_line_not_point (line_through_left P A) hD,
    have hAD := point_in_line_not_point (line_through_right P A) hD,
    exact ⟨hA, hPD, hAD, hD⟩,
  }
  
  
  
end
import tutorial_world.level06_intro --hide
open IncidencePlane --hide

/-
Using the lemma specified before, we are going to prove the next incidence theorem.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

theorem exists_point_not_in_line (l : Line Ω) : ∃ (P : Ω), P ∉ l := --hide
begin --hide
  rcases (@existence Ω _) with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩, --hide
  by_cases hA : A ∈ l, --hide
  { --hide
    by_cases hB : B ∈ l, --hide
    { --hide
      use C, --hide
      have ltA := line_through_left A B, --hide
      have ltB := line_through_right A B, --hide
      have : line_through A B = l, --hide
      { --hide
        exact equal_lines_of_contain_two_points hAB ltA hA ltB hB, --hide
      }, --hide
      rw ← this, --hide
      exact h, --hide
    }, --hide
    { --hide
      use B, --hide
    } --hide
  }, --hide
  { --hide
    use A, --hide
  } --hide
end --hide

lemma point_in_line_not_point {P Q: Ω} {r : Line Ω} (hP : P ∈ r) (hQ : Q ∉ r): P ≠ Q := --hide
begin --hide
  intro H, --hide
  exact hQ (by rwa ← H), --hide
end --hide

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
    have := exists_point_not_in_line (line_through' P A),
    cases this with D hD,
    use A, use D,
    have hPD := point_in_line_not_point (line_through_left P A) hD,
    have hAD := point_in_line_not_point (line_through_right P A) hD,
    exact ⟨hA, hPD, hAD, hD⟩,
  }
  
  
  
end

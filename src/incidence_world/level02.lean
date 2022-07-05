import tutorial_world.incidenceplane --hide
import incidence_world.level01 --hide
import tutorial_world.level06_intro --hide
open IncidencePlane --hide

/-
Now that we have introduced the basic LEAN tactic is time to prove our 
first theorems. We will start with some of the theorems you have seen 
in the theory classes using incidence axioms.

To prove this theorem we will need the lemma, that commes directly from the
incidence axioms,

lemma line_through_left (P Q : Ω) : P ∈ (line_through P Q)

Similarly, we will also have the lemma

lemma line_through_right (P Q : Ω) : Q ∈ (line_through P Q)
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Hint : Click here for a hint, in case you get stuck.
Remember that you can use the lemmas proved before!
-/

/- Theorem :
Giving a line there exists a point that it is not in it.
-/
theorem exist_point_not_in_line (l : Line Ω) : ∃ (P : Ω), P ∉ l :=
begin
  rcases (@existence Ω _) with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  by_cases hA : A ∈ l,
  {
    by_cases hB : B ∈ l,
    {
      use C,
      have ltA := line_through_left A B,
      have ltB := line_through_right A B,
      have : line_through A B = l,
      {
        exact equal_lines_of_contain_two_points hAB ltA hA ltB hB,
      },
      rw ← this,
      exact h,
    },
    {
      use B,
    }
  },
  {
    use A,
  }

  
  
end
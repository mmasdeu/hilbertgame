import tutorial_world.level06_intro --hide
open IncidencePlane --hide

/-
Now that we have introduced the basic *LEAN* tactics, 
let's move on to proving our first theorems.
We will start with some of the theorems you have seen 
in the theory classes using incidence axioms.

To prove this theorem we will need to use two (sub)axioms
(`line_through_left` and `line_through_right`) that you can find
in the side bar.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
Given a line, there exists a point not in it.
-/
lemma exists_point_not_in_line (ℓ : Line Ω) : ∃ (P : Ω), P ∉ ℓ :=
begin
  rcases (@existence Ω _) with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  by_cases hA : A ∈ ℓ,
  {
    by_cases hB : B ∈ ℓ,
    {
      use C,
      have ltA := line_through_left A B,
      have ltB := line_through_right A B,
      have : line_through A B = ℓ,
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
import tutorial_world.incidenceplane --hide
import .level01 --hide
open IncidencePlane --hide

/-
In this level we introduce the new tactic `have`. It is used to add a new hypothesis
to the context (of course, you will have to prove it!). This is sometimes useful to
structure our proofs. In this particular level, it is convenient to prove first that
`r = line_through B C`, then that `s = line_through B C` and that allows us to
finish the prove very easily.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
If two lines r and s, share two diferent ponts A anb B, then they are equal.
-/
lemma exist_point_not_in_line {l : Line Ω} : ∃ (P : Ω), P ∉ l :=
begin
  rcases (@existence Ω _) with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  by_cases hA : A ∈ l,
  {
    by_cases hB : B ∈ l,
    {
      use C,
      --intro H,
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
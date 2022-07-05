import tutorial_world.incidenceplane --hide
open IncidencePlane --hide

/-
To prove some of the theorems in this world we need to introduce the `by_cases` tactic.
This tactic will split the main goal into two cases, assuming a statement on
the first case and his negation on the second.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
Either a point is in a line or it is not.
-/
lemma point_in_line_or_not {A : Ω}	{r : Line Ω} : A ∈ r ∨ A ∉ r :=
begin
  by_cases h : A ∈ r,
  { 
    left,
    exact h,
  },
  { 
    right,
    exact h,
  }


  
end

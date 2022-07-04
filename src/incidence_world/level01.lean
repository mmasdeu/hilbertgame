import tutorial_world.incidenceplane --hide
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
lemma equal_lines_of_contain_two_points {A B : Ω}	{r s : Line Ω} (hAB: A ≠ B)	
(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :	r = s :=
begin
  rw incidence hAB hAr hBr,
  rw incidence hAB hAs hBs,


  
end

import tutorial_world.incidenceplane --hide
import .level04 --hide
open IncidencePlane --hide

/-
As we have done with the last theorem, to prove the next, we need to first prove
a basic lemma that will help us simplify the proof.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
If two lines `r` and `s` do not share a point, then they are not equal.
-/
lemma if_pont_in_line_and_not_in_other_diferent {P : Ω} {r l : Line Ω} (hPr : P ∈ r)
(hPl : P ∉ l): r ≠ l :=
begin
  intro H,
  rw H at hPr,
  exact hPl hPr,
  
  
  
  
end
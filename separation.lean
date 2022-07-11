import basic
open IncidencePlane

noncomputable theory
open_locale classical

variables {Ω : Type} [IncidencePlane Ω]
variables {A B C P Q R : Ω}
variables {ℓ r s t : Line Ω}

lemma same_side_trans_of_noncollinear (h : ¬ collinear ({A, C, B} : set Ω)):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  sorry
end

-- added
lemma line_through_from_and (P Q : Ω) (ℓ : Line Ω) (h1 : P ≠ Q)
(h2 : P ∈ ℓ ∧ Q ∈ ℓ) : ℓ = line_through P Q :=
begin
cases h2 with hP hQ,
exact incidence h1 hP hQ,
end

-- added
lemma point_in_line_not_point {P Q: Ω} {r : Line Ω} (hP : P ∈ r) (hQ : Q ∉ r): P ≠ Q :=
begin
  intro h1,
  apply hQ,
  rw ← h1,
  exact hP,
end

lemma auxiliary_point (ℓ : Line Ω) (h : collinear ({A, B, C} : set Ω)) (hA : A ∉ ℓ) (hB : B ∉ ℓ)
  (hC : C ∉ ℓ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)  :
  ∃ (D E : Ω), D ∈ ℓ ∧ ¬ E ∈ ℓ ∧ same_side ℓ A E ∧ (D * A * E) ∧
  ¬ collinear ({A, B, E} : set Ω) ∧
  ¬ collinear ({E, C, B} : set Ω) ∧
  ¬ collinear ({A, C, E} : set Ω)  :=
begin
--  cases h,
--  specialize h_h,
  rcases (exists_point_on_line ℓ) with ⟨D, hD⟩,
  have f:= point_in_line_not_point hD hA,
  rcases (point_on_ray f) with ⟨E, hE⟩,
  use D, use E,
  repeat {split},
  assumption,
  {
    intro hc,
    apply hA,
    -- prove that a is in the line through D and E 
  -- use have that line through D E is l, then you can prove with use
  -- bc it's an equality
    have g1 : ℓ = line_through D A,
    {
      apply line_through_from_and D A ℓ f,
      split,
      exact hD,
      exact between_points_share_line hD hc hE,
      
    },
    have z:= line_through D E = ℓ,
    exact between_points_share_line hD hc hE,
  },
  {
   clarify,
   sorry
  },
  {
    exact hE,
  },
  {
    intro dc,
    unfold collinear at dc,
    simp at dc,
    cases dc with d1 d2,
    cases d2 with d2 d3,
    cases d3 with d3 d4,
    sorry
--    exact between_points_share_line hD hC hE,
  },
  {
   intro fa,
   unfold collinear at fa,
   simp at fa,
   cases fa with f1 f2,
   cases f2 with f2 f3,
   cases f3 with f3 f4,
   library_search,
  },
  {
   intro ea,
   unfold collinear at ea,
   simp at ea,
   cases ea with e1 e2,
   cases e2 with e2 e3,
   cases e3 with e3 e4,
  },

--  rcases (exists_point_on_line ℓ) with ⟨F, hF⟩,
  --have g:= point_in_line_not_point hE hD,

end

lemma same_side_trans_of_collinear (h : collinear ({A, C, B} : set Ω)):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  sorry
end

lemma same_side_trans_general : same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  sorry
end

lemma at_least_two_classes (ℓ : Line Ω):
      ∃ A B : Ω, (A ∉ ℓ) ∧ (B ∉ ℓ) ∧ (¬ same_side ℓ A B) :=
begin
  sorry
end

lemma at_most_two_classes_of_noncollinear (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
    (h : ¬ collinear ({A, B, C} : set Ω)) : same_side ℓ B C :=
begin
  sorry
end

lemma at_most_two_classes_of_collinear (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
    (h : collinear ({A, B, C} : set Ω)) : same_side ℓ B C :=
begin
  sorry
end

lemma at_most_two_classes_general (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C): same_side ℓ B C :=
begin
  sorry
end

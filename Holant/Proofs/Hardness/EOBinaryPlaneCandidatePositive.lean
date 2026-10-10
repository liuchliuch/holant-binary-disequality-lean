import Holant.Proofs.Hardness.EOBinaryPlaneCandidateGadgets
import Holant.Proofs.Hardness.EOBinaryPlaneGramGraphComplex
import Holant.Proofs.Hardness.EOBinaryPlanePositive

/-! The five physical candidate templates are exactly the five coefficient
formulas used by the positive nonsingular producer. The Gram identity retains
the separately supplied conjugate label and has projective scale exactly one. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCandidatePositive
open Holant
namespace C
export EOBinaryPlaneCandidateGadgets (output transpose)
end C
namespace N
export EOBinaryPlaneGramGraphComplex (matrix conjugate output_matrix)
end N
namespace P
export EOBinaryPlanePositive (candidate Good choice choice_good exceptional)
end P
namespace G
export EOBinaryPlaneGram (table determinant)
end G
set_option backward.isDefEq.respectTransparency false

theorem candidate_matrix (a b c d : ℂ) (i : Fin 5) :
    C.output (N.matrix a b c d) i=
      ![N.matrix a b c d,N.matrix a c b d,N.matrix (a^2) (b^2) (c^2) (d^2),
        N.matrix (a*(a+b)) (b*(c+d)) (c*(a+b)) (d*(c+d)),
        N.matrix (a*(a+c)) (b*(b+d)) (c*(a+c)) (d*(b+d))] i := by
  funext x
  fin_cases i <;> cases h0 : x 0 <;> cases h1 : x 1
  all_goals simp [C.output,C.transpose,EOBinaryPlaneChoiceGadgets.output,N.matrix,h0,h1,pow_two]

theorem candidate_gram (a b c d : ℂ) (i : Fin 5) :
    EOBinaryPlaneGramGraph.output (C.output (N.matrix a b c d) i)
      (N.conjugate (C.output (N.matrix a b c d) i))=
        fun x=>(P.candidate a b c d i x : ℂ) := by
  rw [candidate_matrix]
  fin_cases i
  · exact N.output_matrix a b c d
  · exact N.output_matrix a c b d
  · exact N.output_matrix (a^2) (b^2) (c^2) (d^2)
  · exact N.output_matrix (a*(a+b)) (b*(c+d)) (c*(a+b)) (d*(c+d))
  · exact N.output_matrix (a*(a+c)) (b*(b+d)) (c*(a+c)) (d*(b+d))

theorem graph_candidate (a b c d : ℂ) (i : Fin 5) :
    (EOBinaryPlaneGramGraph.network (C.output (N.matrix a b c d) i)
      (N.conjugate (C.output (N.matrix a b c d) i))).denote=
        EOBinaryPlaneCore.lift (fun x=>(P.candidate a b c d i x : ℂ)) := by
  rw [EOBinaryPlaneGramGraph.denote,candidate_gram]

/-- The selected actual graph realizes precisely the positive table produced
by full-support nontractability, provided the two named labels are interpreted.
Access to the conjugate interpretation is not an assumption of availability. -/
theorem chosen_graph (a b c d : ℂ) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hd : G.determinant a b c d≠0) (he : ¬P.exceptional a b c d) :
    P.Good (P.candidate a b c d (P.choice a b c d)) ∧
      (EOBinaryPlaneGramGraph.network (C.output (N.matrix a b c d) (P.choice a b c d))
        (N.conjugate (C.output (N.matrix a b c d) (P.choice a b c d)))).denote=
          EOBinaryPlaneCore.lift (fun x=>(P.candidate a b c d (P.choice a b c d) x : ℂ)) :=
  ⟨P.choice_good a b c d ha hb hc hd he,graph_candidate a b c d (P.choice a b c d)⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCandidatePositive

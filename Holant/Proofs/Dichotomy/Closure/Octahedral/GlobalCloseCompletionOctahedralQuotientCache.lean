import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralQuotientData
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneCover
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralQuotientPairChecks1
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralQuotientPairChecks2
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralQuotientPairChecks3

/-! Exact arithmetic cache for the same canonical-pair projections. Every
cached pairing is bound above to its original marked root coordinates. -/
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.PlatonicIncidence

def cachedProjected (f : Form) (t : Fin 122) (r : Fin 24) : Fin 2→Scalar :=
  ![RankThree.pairTable f (canonicalPair t 0) r,
    RankThree.pairTable f (canonicalPair t 1) r]

theorem cachedProjected_eq (f : Form) (t : Fin 122) (r : Fin 24) :
    cachedProjected f t r=projected f t r := by
  have he (i j : Fin 24) : RankThree.pairTable f i j=rawPair (rawPoint f i) (rawPoint f j) := by
    fin_cases f
    · exact RankThree.pair_table_exact i j
    · exact RankThree.quotient_pair_exact_1 i j
    · exact RankThree.quotient_pair_exact_2 i j
    · exact RankThree.quotient_pair_exact_3 i j
  simp only [cachedProjected,projected,he]

def cachedIndices (f : Form) (t : Fin 122) : Finset (Fin 24) :=
  Finset.univ.filter fun r => cachedProjected f t r ≠ 0 ∧
    ∀s : Fin 24,s.val<r.val → cachedProjected f t s ≠ 0 →
      cross (cachedProjected f t r) (cachedProjected f t s) ≠ 0

theorem cachedIndices_eq (f : Form) (t : Fin 122) :
    cachedIndices f t=projectedIndices f t := by
  simp only [cachedIndices,projectedIndices,cachedProjected_eq]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo.QuotientEnumeration

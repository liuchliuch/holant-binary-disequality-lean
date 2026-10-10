import Holant.Certificates.OctahedralSeparator.Data

/-! Literal checks against paper1.tex lines12663/12666.  The source fixes the
same Q2=[[0,1],[-1,0]] at line1001.  With its displayed H_dt/H_td and its
H⁻¹ U H convention, the two displayed plus-sign mark identities are false.
These certificates retain all matrices and scales exactly; no source is edited. -/
namespace Holant.Certificates.OctahedralSeparator.SourceErrata
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem dt_plus_actual : theta 2 (q 2+q 3) = ms root (q 2) := by decide +kernel

theorem dt_plus_not_printed : theta 2 (q 2+q 3) ≠ ms root (q 3) := by decide +kernel

theorem dt_corrected_mark : theta 2 (q 2-q 3) = ms (-root) (q 3) := by decide +kernel

theorem td_plus_actual : theta 3 (q 1+q 2) = ms root (q 2) := by decide +kernel

theorem td_plus_not_printed : theta 3 (q 1+q 2) ≠ ms root (q 1) := by decide +kernel

theorem td_corrected_mark : theta 3 (q 1-q 2) = ms root (q 1) := by decide +kernel

end Holant.Certificates.OctahedralSeparator.SourceErrata

import Holant.Certificates.PlatonicAtlas.LineGraphTetrahedralRows0
import Holant.Certificates.PlatonicAtlas.LineGraphTetrahedralCover0
import Holant.Certificates.PlatonicAtlas.LineGraphOctahedralRows0
import Holant.Certificates.PlatonicAtlas.LineGraphOctahedralRows1
import Holant.Certificates.PlatonicAtlas.LineGraphOctahedralRows2
import Holant.Certificates.PlatonicAtlas.LineGraphOctahedralRows3
import Holant.Certificates.PlatonicAtlas.LineGraphOctahedralCover0
import Holant.Certificates.PlatonicAtlas.LineGraphOctahedralCover1
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows0
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows1
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows2
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows3
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows4
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows5
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows6
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows7
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows8
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows9
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows10
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows11
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows12
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows13
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows14
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows15
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralRows16
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover0
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover1
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover2
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover3
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover4
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover5
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover6
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover7
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover8
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover9
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover10
import Holant.Certificates.PlatonicAtlas.LineGraphIcosahedralCover11

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem rich_rows (g : PlatonicModel) (i : Fin (richCount g)) : RichEntry g i := by
  cases g
  · exact tetrahedralRows0_entry i (by omega) i.isLt
  · by_cases h0 : i.val<16
    · exact octahedralRows0_entry i (by omega) h0
    by_cases h1 : i.val<32
    · exact octahedralRows1_entry i (by omega) h1
    by_cases h2 : i.val<48
    · exact octahedralRows2_entry i (by omega) h2
    exact octahedralRows3_entry i (by omega) i.isLt
  · by_cases h0 : i.val<16
    · exact icosahedralRows0_entry i (by omega) h0
    by_cases h1 : i.val<32
    · exact icosahedralRows1_entry i (by omega) h1
    by_cases h2 : i.val<48
    · exact icosahedralRows2_entry i (by omega) h2
    by_cases h3 : i.val<64
    · exact icosahedralRows3_entry i (by omega) h3
    by_cases h4 : i.val<80
    · exact icosahedralRows4_entry i (by omega) h4
    by_cases h5 : i.val<96
    · exact icosahedralRows5_entry i (by omega) h5
    by_cases h6 : i.val<112
    · exact icosahedralRows6_entry i (by omega) h6
    by_cases h7 : i.val<128
    · exact icosahedralRows7_entry i (by omega) h7
    by_cases h8 : i.val<144
    · exact icosahedralRows8_entry i (by omega) h8
    by_cases h9 : i.val<160
    · exact icosahedralRows9_entry i (by omega) h9
    by_cases h10 : i.val<176
    · exact icosahedralRows10_entry i (by omega) h10
    by_cases h11 : i.val<192
    · exact icosahedralRows11_entry i (by omega) h11
    by_cases h12 : i.val<208
    · exact icosahedralRows12_entry i (by omega) h12
    by_cases h13 : i.val<224
    · exact icosahedralRows13_entry i (by omega) h13
    by_cases h14 : i.val<240
    · exact icosahedralRows14_entry i (by omega) h14
    by_cases h15 : i.val<256
    · exact icosahedralRows15_entry i (by omega) h15
    exact icosahedralRows16_entry i (by omega) i.isLt

theorem rich_cover (g : PlatonicModel) (i : Fin (secantCount g)) : RichCoverage g i := by
  cases g
  · exact tetrahedralCover0_entry i (by omega) i.isLt
  · by_cases h0 : i.val<64
    · exact octahedralCover0_entry i (by omega) h0
    exact octahedralCover1_entry i (by omega) i.isLt
  · by_cases h0 : i.val<64
    · exact icosahedralCover0_entry i (by omega) h0
    by_cases h1 : i.val<128
    · exact icosahedralCover1_entry i (by omega) h1
    by_cases h2 : i.val<192
    · exact icosahedralCover2_entry i (by omega) h2
    by_cases h3 : i.val<256
    · exact icosahedralCover3_entry i (by omega) h3
    by_cases h4 : i.val<320
    · exact icosahedralCover4_entry i (by omega) h4
    by_cases h5 : i.val<384
    · exact icosahedralCover5_entry i (by omega) h5
    by_cases h6 : i.val<448
    · exact icosahedralCover6_entry i (by omega) h6
    by_cases h7 : i.val<512
    · exact icosahedralCover7_entry i (by omega) h7
    by_cases h8 : i.val<576
    · exact icosahedralCover8_entry i (by omega) h8
    by_cases h9 : i.val<640
    · exact icosahedralCover9_entry i (by omega) h9
    by_cases h10 : i.val<704
    · exact icosahedralCover10_entry i (by omega) h10
    exact icosahedralCover11_entry i (by omega) i.isLt

theorem richIndex_injective (g : PlatonicModel) : Function.Injective (richIndex g) := by
  have hs : StrictMono (richIndex g) := by
    cases g <;> apply Fin.strictMono_iff_lt_succ.mpr <;> decide +kernel
  exact hs.injective

theorem rich_degree_sum (g : PlatonicModel) : (∑i,richDegree g i)=match g with
    | .tetrahedral => 144
    | .octahedral => 1008
    | .icosahedral => 14400 := by
  cases g <;> decide +kernel

end Holant.Certificates.PlatonicAtlas

import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk00
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk01
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk02
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk03
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk04
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk05
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk06
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk07
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk08
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk09
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk10
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk11
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk12
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk13
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk14
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk15
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk16
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk17
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk18
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk19
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk20
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk21
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk22
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk23
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk24
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk25
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk26
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk27
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk28
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk29
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk30
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk31
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk32
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk33
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk34
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk35
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk36
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk37
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk38
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk39
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk40
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk41
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk42
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk43
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk44
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk45
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk46
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk47
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk48
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk49
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk50
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk51
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk52
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk53
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk54
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk55
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk56
import Holant.Pauli.ExoticKlein.SixPortOrbitBlocks.Chunk57

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option Elab.async false

def chunkSourceBlock (c : Fin 58) (i : Fin 16) : Fin 920 := Fin.ofNat 920 (16*c.val+i.val)

def orbitChunk00Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData000, orbitBlockData001, orbitBlockData002, orbitBlockData003, orbitBlockData004, orbitBlockData005, orbitBlockData006, orbitBlockData007, orbitBlockData008, orbitBlockData009, orbitBlockData010, orbitBlockData011, orbitBlockData012, orbitBlockData013, orbitBlockData014, orbitBlockData015]

theorem orbitChunk00_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 0 i) (orbitChunk00Data i) = true := by
  fin_cases i
  · exact orbitBlock000_checked
  · exact orbitBlock001_checked
  · exact orbitBlock002_checked
  · exact orbitBlock003_checked
  · exact orbitBlock004_checked
  · exact orbitBlock005_checked
  · exact orbitBlock006_checked
  · exact orbitBlock007_checked
  · exact orbitBlock008_checked
  · exact orbitBlock009_checked
  · exact orbitBlock010_checked
  · exact orbitBlock011_checked
  · exact orbitBlock012_checked
  · exact orbitBlock013_checked
  · exact orbitBlock014_checked
  · exact orbitBlock015_checked

def orbitChunk01Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData016, orbitBlockData017, orbitBlockData018, orbitBlockData019, orbitBlockData020, orbitBlockData021, orbitBlockData022, orbitBlockData023, orbitBlockData024, orbitBlockData025, orbitBlockData026, orbitBlockData027, orbitBlockData028, orbitBlockData029, orbitBlockData030, orbitBlockData031]

theorem orbitChunk01_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 1 i) (orbitChunk01Data i) = true := by
  fin_cases i
  · exact orbitBlock016_checked
  · exact orbitBlock017_checked
  · exact orbitBlock018_checked
  · exact orbitBlock019_checked
  · exact orbitBlock020_checked
  · exact orbitBlock021_checked
  · exact orbitBlock022_checked
  · exact orbitBlock023_checked
  · exact orbitBlock024_checked
  · exact orbitBlock025_checked
  · exact orbitBlock026_checked
  · exact orbitBlock027_checked
  · exact orbitBlock028_checked
  · exact orbitBlock029_checked
  · exact orbitBlock030_checked
  · exact orbitBlock031_checked

def orbitChunk02Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData032, orbitBlockData033, orbitBlockData034, orbitBlockData035, orbitBlockData036, orbitBlockData037, orbitBlockData038, orbitBlockData039, orbitBlockData040, orbitBlockData041, orbitBlockData042, orbitBlockData043, orbitBlockData044, orbitBlockData045, orbitBlockData046, orbitBlockData047]

theorem orbitChunk02_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 2 i) (orbitChunk02Data i) = true := by
  fin_cases i
  · exact orbitBlock032_checked
  · exact orbitBlock033_checked
  · exact orbitBlock034_checked
  · exact orbitBlock035_checked
  · exact orbitBlock036_checked
  · exact orbitBlock037_checked
  · exact orbitBlock038_checked
  · exact orbitBlock039_checked
  · exact orbitBlock040_checked
  · exact orbitBlock041_checked
  · exact orbitBlock042_checked
  · exact orbitBlock043_checked
  · exact orbitBlock044_checked
  · exact orbitBlock045_checked
  · exact orbitBlock046_checked
  · exact orbitBlock047_checked

def orbitChunk03Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData048, orbitBlockData049, orbitBlockData050, orbitBlockData051, orbitBlockData052, orbitBlockData053, orbitBlockData054, orbitBlockData055, orbitBlockData056, orbitBlockData057, orbitBlockData058, orbitBlockData059, orbitBlockData060, orbitBlockData061, orbitBlockData062, orbitBlockData063]

theorem orbitChunk03_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 3 i) (orbitChunk03Data i) = true := by
  fin_cases i
  · exact orbitBlock048_checked
  · exact orbitBlock049_checked
  · exact orbitBlock050_checked
  · exact orbitBlock051_checked
  · exact orbitBlock052_checked
  · exact orbitBlock053_checked
  · exact orbitBlock054_checked
  · exact orbitBlock055_checked
  · exact orbitBlock056_checked
  · exact orbitBlock057_checked
  · exact orbitBlock058_checked
  · exact orbitBlock059_checked
  · exact orbitBlock060_checked
  · exact orbitBlock061_checked
  · exact orbitBlock062_checked
  · exact orbitBlock063_checked

def orbitChunk04Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData064, orbitBlockData065, orbitBlockData066, orbitBlockData067, orbitBlockData068, orbitBlockData069, orbitBlockData070, orbitBlockData071, orbitBlockData072, orbitBlockData073, orbitBlockData074, orbitBlockData075, orbitBlockData076, orbitBlockData077, orbitBlockData078, orbitBlockData079]

theorem orbitChunk04_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 4 i) (orbitChunk04Data i) = true := by
  fin_cases i
  · exact orbitBlock064_checked
  · exact orbitBlock065_checked
  · exact orbitBlock066_checked
  · exact orbitBlock067_checked
  · exact orbitBlock068_checked
  · exact orbitBlock069_checked
  · exact orbitBlock070_checked
  · exact orbitBlock071_checked
  · exact orbitBlock072_checked
  · exact orbitBlock073_checked
  · exact orbitBlock074_checked
  · exact orbitBlock075_checked
  · exact orbitBlock076_checked
  · exact orbitBlock077_checked
  · exact orbitBlock078_checked
  · exact orbitBlock079_checked

def orbitChunk05Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData080, orbitBlockData081, orbitBlockData082, orbitBlockData083, orbitBlockData084, orbitBlockData085, orbitBlockData086, orbitBlockData087, orbitBlockData088, orbitBlockData089, orbitBlockData090, orbitBlockData091, orbitBlockData092, orbitBlockData093, orbitBlockData094, orbitBlockData095]

theorem orbitChunk05_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 5 i) (orbitChunk05Data i) = true := by
  fin_cases i
  · exact orbitBlock080_checked
  · exact orbitBlock081_checked
  · exact orbitBlock082_checked
  · exact orbitBlock083_checked
  · exact orbitBlock084_checked
  · exact orbitBlock085_checked
  · exact orbitBlock086_checked
  · exact orbitBlock087_checked
  · exact orbitBlock088_checked
  · exact orbitBlock089_checked
  · exact orbitBlock090_checked
  · exact orbitBlock091_checked
  · exact orbitBlock092_checked
  · exact orbitBlock093_checked
  · exact orbitBlock094_checked
  · exact orbitBlock095_checked

def orbitChunk06Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData096, orbitBlockData097, orbitBlockData098, orbitBlockData099, orbitBlockData100, orbitBlockData101, orbitBlockData102, orbitBlockData103, orbitBlockData104, orbitBlockData105, orbitBlockData106, orbitBlockData107, orbitBlockData108, orbitBlockData109, orbitBlockData110, orbitBlockData111]

theorem orbitChunk06_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 6 i) (orbitChunk06Data i) = true := by
  fin_cases i
  · exact orbitBlock096_checked
  · exact orbitBlock097_checked
  · exact orbitBlock098_checked
  · exact orbitBlock099_checked
  · exact orbitBlock100_checked
  · exact orbitBlock101_checked
  · exact orbitBlock102_checked
  · exact orbitBlock103_checked
  · exact orbitBlock104_checked
  · exact orbitBlock105_checked
  · exact orbitBlock106_checked
  · exact orbitBlock107_checked
  · exact orbitBlock108_checked
  · exact orbitBlock109_checked
  · exact orbitBlock110_checked
  · exact orbitBlock111_checked

def orbitChunk07Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData112, orbitBlockData113, orbitBlockData114, orbitBlockData115, orbitBlockData116, orbitBlockData117, orbitBlockData118, orbitBlockData119, orbitBlockData120, orbitBlockData121, orbitBlockData122, orbitBlockData123, orbitBlockData124, orbitBlockData125, orbitBlockData126, orbitBlockData127]

theorem orbitChunk07_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 7 i) (orbitChunk07Data i) = true := by
  fin_cases i
  · exact orbitBlock112_checked
  · exact orbitBlock113_checked
  · exact orbitBlock114_checked
  · exact orbitBlock115_checked
  · exact orbitBlock116_checked
  · exact orbitBlock117_checked
  · exact orbitBlock118_checked
  · exact orbitBlock119_checked
  · exact orbitBlock120_checked
  · exact orbitBlock121_checked
  · exact orbitBlock122_checked
  · exact orbitBlock123_checked
  · exact orbitBlock124_checked
  · exact orbitBlock125_checked
  · exact orbitBlock126_checked
  · exact orbitBlock127_checked

def orbitChunk08Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData128, orbitBlockData129, orbitBlockData130, orbitBlockData131, orbitBlockData132, orbitBlockData133, orbitBlockData134, orbitBlockData135, orbitBlockData136, orbitBlockData137, orbitBlockData138, orbitBlockData139, orbitBlockData140, orbitBlockData141, orbitBlockData142, orbitBlockData143]

theorem orbitChunk08_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 8 i) (orbitChunk08Data i) = true := by
  fin_cases i
  · exact orbitBlock128_checked
  · exact orbitBlock129_checked
  · exact orbitBlock130_checked
  · exact orbitBlock131_checked
  · exact orbitBlock132_checked
  · exact orbitBlock133_checked
  · exact orbitBlock134_checked
  · exact orbitBlock135_checked
  · exact orbitBlock136_checked
  · exact orbitBlock137_checked
  · exact orbitBlock138_checked
  · exact orbitBlock139_checked
  · exact orbitBlock140_checked
  · exact orbitBlock141_checked
  · exact orbitBlock142_checked
  · exact orbitBlock143_checked

def orbitChunk09Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData144, orbitBlockData145, orbitBlockData146, orbitBlockData147, orbitBlockData148, orbitBlockData149, orbitBlockData150, orbitBlockData151, orbitBlockData152, orbitBlockData153, orbitBlockData154, orbitBlockData155, orbitBlockData156, orbitBlockData157, orbitBlockData158, orbitBlockData159]

theorem orbitChunk09_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 9 i) (orbitChunk09Data i) = true := by
  fin_cases i
  · exact orbitBlock144_checked
  · exact orbitBlock145_checked
  · exact orbitBlock146_checked
  · exact orbitBlock147_checked
  · exact orbitBlock148_checked
  · exact orbitBlock149_checked
  · exact orbitBlock150_checked
  · exact orbitBlock151_checked
  · exact orbitBlock152_checked
  · exact orbitBlock153_checked
  · exact orbitBlock154_checked
  · exact orbitBlock155_checked
  · exact orbitBlock156_checked
  · exact orbitBlock157_checked
  · exact orbitBlock158_checked
  · exact orbitBlock159_checked

def orbitChunk10Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData160, orbitBlockData161, orbitBlockData162, orbitBlockData163, orbitBlockData164, orbitBlockData165, orbitBlockData166, orbitBlockData167, orbitBlockData168, orbitBlockData169, orbitBlockData170, orbitBlockData171, orbitBlockData172, orbitBlockData173, orbitBlockData174, orbitBlockData175]

theorem orbitChunk10_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 10 i) (orbitChunk10Data i) = true := by
  fin_cases i
  · exact orbitBlock160_checked
  · exact orbitBlock161_checked
  · exact orbitBlock162_checked
  · exact orbitBlock163_checked
  · exact orbitBlock164_checked
  · exact orbitBlock165_checked
  · exact orbitBlock166_checked
  · exact orbitBlock167_checked
  · exact orbitBlock168_checked
  · exact orbitBlock169_checked
  · exact orbitBlock170_checked
  · exact orbitBlock171_checked
  · exact orbitBlock172_checked
  · exact orbitBlock173_checked
  · exact orbitBlock174_checked
  · exact orbitBlock175_checked

def orbitChunk11Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData176, orbitBlockData177, orbitBlockData178, orbitBlockData179, orbitBlockData180, orbitBlockData181, orbitBlockData182, orbitBlockData183, orbitBlockData184, orbitBlockData185, orbitBlockData186, orbitBlockData187, orbitBlockData188, orbitBlockData189, orbitBlockData190, orbitBlockData191]

theorem orbitChunk11_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 11 i) (orbitChunk11Data i) = true := by
  fin_cases i
  · exact orbitBlock176_checked
  · exact orbitBlock177_checked
  · exact orbitBlock178_checked
  · exact orbitBlock179_checked
  · exact orbitBlock180_checked
  · exact orbitBlock181_checked
  · exact orbitBlock182_checked
  · exact orbitBlock183_checked
  · exact orbitBlock184_checked
  · exact orbitBlock185_checked
  · exact orbitBlock186_checked
  · exact orbitBlock187_checked
  · exact orbitBlock188_checked
  · exact orbitBlock189_checked
  · exact orbitBlock190_checked
  · exact orbitBlock191_checked

def orbitChunk12Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData192, orbitBlockData193, orbitBlockData194, orbitBlockData195, orbitBlockData196, orbitBlockData197, orbitBlockData198, orbitBlockData199, orbitBlockData200, orbitBlockData201, orbitBlockData202, orbitBlockData203, orbitBlockData204, orbitBlockData205, orbitBlockData206, orbitBlockData207]

theorem orbitChunk12_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 12 i) (orbitChunk12Data i) = true := by
  fin_cases i
  · exact orbitBlock192_checked
  · exact orbitBlock193_checked
  · exact orbitBlock194_checked
  · exact orbitBlock195_checked
  · exact orbitBlock196_checked
  · exact orbitBlock197_checked
  · exact orbitBlock198_checked
  · exact orbitBlock199_checked
  · exact orbitBlock200_checked
  · exact orbitBlock201_checked
  · exact orbitBlock202_checked
  · exact orbitBlock203_checked
  · exact orbitBlock204_checked
  · exact orbitBlock205_checked
  · exact orbitBlock206_checked
  · exact orbitBlock207_checked

def orbitChunk13Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData208, orbitBlockData209, orbitBlockData210, orbitBlockData211, orbitBlockData212, orbitBlockData213, orbitBlockData214, orbitBlockData215, orbitBlockData216, orbitBlockData217, orbitBlockData218, orbitBlockData219, orbitBlockData220, orbitBlockData221, orbitBlockData222, orbitBlockData223]

theorem orbitChunk13_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 13 i) (orbitChunk13Data i) = true := by
  fin_cases i
  · exact orbitBlock208_checked
  · exact orbitBlock209_checked
  · exact orbitBlock210_checked
  · exact orbitBlock211_checked
  · exact orbitBlock212_checked
  · exact orbitBlock213_checked
  · exact orbitBlock214_checked
  · exact orbitBlock215_checked
  · exact orbitBlock216_checked
  · exact orbitBlock217_checked
  · exact orbitBlock218_checked
  · exact orbitBlock219_checked
  · exact orbitBlock220_checked
  · exact orbitBlock221_checked
  · exact orbitBlock222_checked
  · exact orbitBlock223_checked

def orbitChunk14Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData224, orbitBlockData225, orbitBlockData226, orbitBlockData227, orbitBlockData228, orbitBlockData229, orbitBlockData230, orbitBlockData231, orbitBlockData232, orbitBlockData233, orbitBlockData234, orbitBlockData235, orbitBlockData236, orbitBlockData237, orbitBlockData238, orbitBlockData239]

theorem orbitChunk14_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 14 i) (orbitChunk14Data i) = true := by
  fin_cases i
  · exact orbitBlock224_checked
  · exact orbitBlock225_checked
  · exact orbitBlock226_checked
  · exact orbitBlock227_checked
  · exact orbitBlock228_checked
  · exact orbitBlock229_checked
  · exact orbitBlock230_checked
  · exact orbitBlock231_checked
  · exact orbitBlock232_checked
  · exact orbitBlock233_checked
  · exact orbitBlock234_checked
  · exact orbitBlock235_checked
  · exact orbitBlock236_checked
  · exact orbitBlock237_checked
  · exact orbitBlock238_checked
  · exact orbitBlock239_checked

def orbitChunk15Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData240, orbitBlockData241, orbitBlockData242, orbitBlockData243, orbitBlockData244, orbitBlockData245, orbitBlockData246, orbitBlockData247, orbitBlockData248, orbitBlockData249, orbitBlockData250, orbitBlockData251, orbitBlockData252, orbitBlockData253, orbitBlockData254, orbitBlockData255]

theorem orbitChunk15_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 15 i) (orbitChunk15Data i) = true := by
  fin_cases i
  · exact orbitBlock240_checked
  · exact orbitBlock241_checked
  · exact orbitBlock242_checked
  · exact orbitBlock243_checked
  · exact orbitBlock244_checked
  · exact orbitBlock245_checked
  · exact orbitBlock246_checked
  · exact orbitBlock247_checked
  · exact orbitBlock248_checked
  · exact orbitBlock249_checked
  · exact orbitBlock250_checked
  · exact orbitBlock251_checked
  · exact orbitBlock252_checked
  · exact orbitBlock253_checked
  · exact orbitBlock254_checked
  · exact orbitBlock255_checked

def orbitChunk16Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData256, orbitBlockData257, orbitBlockData258, orbitBlockData259, orbitBlockData260, orbitBlockData261, orbitBlockData262, orbitBlockData263, orbitBlockData264, orbitBlockData265, orbitBlockData266, orbitBlockData267, orbitBlockData268, orbitBlockData269, orbitBlockData270, orbitBlockData271]

theorem orbitChunk16_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 16 i) (orbitChunk16Data i) = true := by
  fin_cases i
  · exact orbitBlock256_checked
  · exact orbitBlock257_checked
  · exact orbitBlock258_checked
  · exact orbitBlock259_checked
  · exact orbitBlock260_checked
  · exact orbitBlock261_checked
  · exact orbitBlock262_checked
  · exact orbitBlock263_checked
  · exact orbitBlock264_checked
  · exact orbitBlock265_checked
  · exact orbitBlock266_checked
  · exact orbitBlock267_checked
  · exact orbitBlock268_checked
  · exact orbitBlock269_checked
  · exact orbitBlock270_checked
  · exact orbitBlock271_checked

def orbitChunk17Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData272, orbitBlockData273, orbitBlockData274, orbitBlockData275, orbitBlockData276, orbitBlockData277, orbitBlockData278, orbitBlockData279, orbitBlockData280, orbitBlockData281, orbitBlockData282, orbitBlockData283, orbitBlockData284, orbitBlockData285, orbitBlockData286, orbitBlockData287]

theorem orbitChunk17_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 17 i) (orbitChunk17Data i) = true := by
  fin_cases i
  · exact orbitBlock272_checked
  · exact orbitBlock273_checked
  · exact orbitBlock274_checked
  · exact orbitBlock275_checked
  · exact orbitBlock276_checked
  · exact orbitBlock277_checked
  · exact orbitBlock278_checked
  · exact orbitBlock279_checked
  · exact orbitBlock280_checked
  · exact orbitBlock281_checked
  · exact orbitBlock282_checked
  · exact orbitBlock283_checked
  · exact orbitBlock284_checked
  · exact orbitBlock285_checked
  · exact orbitBlock286_checked
  · exact orbitBlock287_checked

def orbitChunk18Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData288, orbitBlockData289, orbitBlockData290, orbitBlockData291, orbitBlockData292, orbitBlockData293, orbitBlockData294, orbitBlockData295, orbitBlockData296, orbitBlockData297, orbitBlockData298, orbitBlockData299, orbitBlockData300, orbitBlockData301, orbitBlockData302, orbitBlockData303]

theorem orbitChunk18_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 18 i) (orbitChunk18Data i) = true := by
  fin_cases i
  · exact orbitBlock288_checked
  · exact orbitBlock289_checked
  · exact orbitBlock290_checked
  · exact orbitBlock291_checked
  · exact orbitBlock292_checked
  · exact orbitBlock293_checked
  · exact orbitBlock294_checked
  · exact orbitBlock295_checked
  · exact orbitBlock296_checked
  · exact orbitBlock297_checked
  · exact orbitBlock298_checked
  · exact orbitBlock299_checked
  · exact orbitBlock300_checked
  · exact orbitBlock301_checked
  · exact orbitBlock302_checked
  · exact orbitBlock303_checked

def orbitChunk19Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData304, orbitBlockData305, orbitBlockData306, orbitBlockData307, orbitBlockData308, orbitBlockData309, orbitBlockData310, orbitBlockData311, orbitBlockData312, orbitBlockData313, orbitBlockData314, orbitBlockData315, orbitBlockData316, orbitBlockData317, orbitBlockData318, orbitBlockData319]

theorem orbitChunk19_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 19 i) (orbitChunk19Data i) = true := by
  fin_cases i
  · exact orbitBlock304_checked
  · exact orbitBlock305_checked
  · exact orbitBlock306_checked
  · exact orbitBlock307_checked
  · exact orbitBlock308_checked
  · exact orbitBlock309_checked
  · exact orbitBlock310_checked
  · exact orbitBlock311_checked
  · exact orbitBlock312_checked
  · exact orbitBlock313_checked
  · exact orbitBlock314_checked
  · exact orbitBlock315_checked
  · exact orbitBlock316_checked
  · exact orbitBlock317_checked
  · exact orbitBlock318_checked
  · exact orbitBlock319_checked

def orbitChunk20Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData320, orbitBlockData321, orbitBlockData322, orbitBlockData323, orbitBlockData324, orbitBlockData325, orbitBlockData326, orbitBlockData327, orbitBlockData328, orbitBlockData329, orbitBlockData330, orbitBlockData331, orbitBlockData332, orbitBlockData333, orbitBlockData334, orbitBlockData335]

theorem orbitChunk20_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 20 i) (orbitChunk20Data i) = true := by
  fin_cases i
  · exact orbitBlock320_checked
  · exact orbitBlock321_checked
  · exact orbitBlock322_checked
  · exact orbitBlock323_checked
  · exact orbitBlock324_checked
  · exact orbitBlock325_checked
  · exact orbitBlock326_checked
  · exact orbitBlock327_checked
  · exact orbitBlock328_checked
  · exact orbitBlock329_checked
  · exact orbitBlock330_checked
  · exact orbitBlock331_checked
  · exact orbitBlock332_checked
  · exact orbitBlock333_checked
  · exact orbitBlock334_checked
  · exact orbitBlock335_checked

def orbitChunk21Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData336, orbitBlockData337, orbitBlockData338, orbitBlockData339, orbitBlockData340, orbitBlockData341, orbitBlockData342, orbitBlockData343, orbitBlockData344, orbitBlockData345, orbitBlockData346, orbitBlockData347, orbitBlockData348, orbitBlockData349, orbitBlockData350, orbitBlockData351]

theorem orbitChunk21_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 21 i) (orbitChunk21Data i) = true := by
  fin_cases i
  · exact orbitBlock336_checked
  · exact orbitBlock337_checked
  · exact orbitBlock338_checked
  · exact orbitBlock339_checked
  · exact orbitBlock340_checked
  · exact orbitBlock341_checked
  · exact orbitBlock342_checked
  · exact orbitBlock343_checked
  · exact orbitBlock344_checked
  · exact orbitBlock345_checked
  · exact orbitBlock346_checked
  · exact orbitBlock347_checked
  · exact orbitBlock348_checked
  · exact orbitBlock349_checked
  · exact orbitBlock350_checked
  · exact orbitBlock351_checked

def orbitChunk22Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData352, orbitBlockData353, orbitBlockData354, orbitBlockData355, orbitBlockData356, orbitBlockData357, orbitBlockData358, orbitBlockData359, orbitBlockData360, orbitBlockData361, orbitBlockData362, orbitBlockData363, orbitBlockData364, orbitBlockData365, orbitBlockData366, orbitBlockData367]

theorem orbitChunk22_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 22 i) (orbitChunk22Data i) = true := by
  fin_cases i
  · exact orbitBlock352_checked
  · exact orbitBlock353_checked
  · exact orbitBlock354_checked
  · exact orbitBlock355_checked
  · exact orbitBlock356_checked
  · exact orbitBlock357_checked
  · exact orbitBlock358_checked
  · exact orbitBlock359_checked
  · exact orbitBlock360_checked
  · exact orbitBlock361_checked
  · exact orbitBlock362_checked
  · exact orbitBlock363_checked
  · exact orbitBlock364_checked
  · exact orbitBlock365_checked
  · exact orbitBlock366_checked
  · exact orbitBlock367_checked

def orbitChunk23Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData368, orbitBlockData369, orbitBlockData370, orbitBlockData371, orbitBlockData372, orbitBlockData373, orbitBlockData374, orbitBlockData375, orbitBlockData376, orbitBlockData377, orbitBlockData378, orbitBlockData379, orbitBlockData380, orbitBlockData381, orbitBlockData382, orbitBlockData383]

theorem orbitChunk23_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 23 i) (orbitChunk23Data i) = true := by
  fin_cases i
  · exact orbitBlock368_checked
  · exact orbitBlock369_checked
  · exact orbitBlock370_checked
  · exact orbitBlock371_checked
  · exact orbitBlock372_checked
  · exact orbitBlock373_checked
  · exact orbitBlock374_checked
  · exact orbitBlock375_checked
  · exact orbitBlock376_checked
  · exact orbitBlock377_checked
  · exact orbitBlock378_checked
  · exact orbitBlock379_checked
  · exact orbitBlock380_checked
  · exact orbitBlock381_checked
  · exact orbitBlock382_checked
  · exact orbitBlock383_checked

def orbitChunk24Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData384, orbitBlockData385, orbitBlockData386, orbitBlockData387, orbitBlockData388, orbitBlockData389, orbitBlockData390, orbitBlockData391, orbitBlockData392, orbitBlockData393, orbitBlockData394, orbitBlockData395, orbitBlockData396, orbitBlockData397, orbitBlockData398, orbitBlockData399]

theorem orbitChunk24_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 24 i) (orbitChunk24Data i) = true := by
  fin_cases i
  · exact orbitBlock384_checked
  · exact orbitBlock385_checked
  · exact orbitBlock386_checked
  · exact orbitBlock387_checked
  · exact orbitBlock388_checked
  · exact orbitBlock389_checked
  · exact orbitBlock390_checked
  · exact orbitBlock391_checked
  · exact orbitBlock392_checked
  · exact orbitBlock393_checked
  · exact orbitBlock394_checked
  · exact orbitBlock395_checked
  · exact orbitBlock396_checked
  · exact orbitBlock397_checked
  · exact orbitBlock398_checked
  · exact orbitBlock399_checked

def orbitChunk25Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData400, orbitBlockData401, orbitBlockData402, orbitBlockData403, orbitBlockData404, orbitBlockData405, orbitBlockData406, orbitBlockData407, orbitBlockData408, orbitBlockData409, orbitBlockData410, orbitBlockData411, orbitBlockData412, orbitBlockData413, orbitBlockData414, orbitBlockData415]

theorem orbitChunk25_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 25 i) (orbitChunk25Data i) = true := by
  fin_cases i
  · exact orbitBlock400_checked
  · exact orbitBlock401_checked
  · exact orbitBlock402_checked
  · exact orbitBlock403_checked
  · exact orbitBlock404_checked
  · exact orbitBlock405_checked
  · exact orbitBlock406_checked
  · exact orbitBlock407_checked
  · exact orbitBlock408_checked
  · exact orbitBlock409_checked
  · exact orbitBlock410_checked
  · exact orbitBlock411_checked
  · exact orbitBlock412_checked
  · exact orbitBlock413_checked
  · exact orbitBlock414_checked
  · exact orbitBlock415_checked

def orbitChunk26Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData416, orbitBlockData417, orbitBlockData418, orbitBlockData419, orbitBlockData420, orbitBlockData421, orbitBlockData422, orbitBlockData423, orbitBlockData424, orbitBlockData425, orbitBlockData426, orbitBlockData427, orbitBlockData428, orbitBlockData429, orbitBlockData430, orbitBlockData431]

theorem orbitChunk26_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 26 i) (orbitChunk26Data i) = true := by
  fin_cases i
  · exact orbitBlock416_checked
  · exact orbitBlock417_checked
  · exact orbitBlock418_checked
  · exact orbitBlock419_checked
  · exact orbitBlock420_checked
  · exact orbitBlock421_checked
  · exact orbitBlock422_checked
  · exact orbitBlock423_checked
  · exact orbitBlock424_checked
  · exact orbitBlock425_checked
  · exact orbitBlock426_checked
  · exact orbitBlock427_checked
  · exact orbitBlock428_checked
  · exact orbitBlock429_checked
  · exact orbitBlock430_checked
  · exact orbitBlock431_checked

def orbitChunk27Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData432, orbitBlockData433, orbitBlockData434, orbitBlockData435, orbitBlockData436, orbitBlockData437, orbitBlockData438, orbitBlockData439, orbitBlockData440, orbitBlockData441, orbitBlockData442, orbitBlockData443, orbitBlockData444, orbitBlockData445, orbitBlockData446, orbitBlockData447]

theorem orbitChunk27_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 27 i) (orbitChunk27Data i) = true := by
  fin_cases i
  · exact orbitBlock432_checked
  · exact orbitBlock433_checked
  · exact orbitBlock434_checked
  · exact orbitBlock435_checked
  · exact orbitBlock436_checked
  · exact orbitBlock437_checked
  · exact orbitBlock438_checked
  · exact orbitBlock439_checked
  · exact orbitBlock440_checked
  · exact orbitBlock441_checked
  · exact orbitBlock442_checked
  · exact orbitBlock443_checked
  · exact orbitBlock444_checked
  · exact orbitBlock445_checked
  · exact orbitBlock446_checked
  · exact orbitBlock447_checked

def orbitChunk28Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData448, orbitBlockData449, orbitBlockData450, orbitBlockData451, orbitBlockData452, orbitBlockData453, orbitBlockData454, orbitBlockData455, orbitBlockData456, orbitBlockData457, orbitBlockData458, orbitBlockData459, orbitBlockData460, orbitBlockData461, orbitBlockData462, orbitBlockData463]

theorem orbitChunk28_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 28 i) (orbitChunk28Data i) = true := by
  fin_cases i
  · exact orbitBlock448_checked
  · exact orbitBlock449_checked
  · exact orbitBlock450_checked
  · exact orbitBlock451_checked
  · exact orbitBlock452_checked
  · exact orbitBlock453_checked
  · exact orbitBlock454_checked
  · exact orbitBlock455_checked
  · exact orbitBlock456_checked
  · exact orbitBlock457_checked
  · exact orbitBlock458_checked
  · exact orbitBlock459_checked
  · exact orbitBlock460_checked
  · exact orbitBlock461_checked
  · exact orbitBlock462_checked
  · exact orbitBlock463_checked

def orbitChunk29Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData464, orbitBlockData465, orbitBlockData466, orbitBlockData467, orbitBlockData468, orbitBlockData469, orbitBlockData470, orbitBlockData471, orbitBlockData472, orbitBlockData473, orbitBlockData474, orbitBlockData475, orbitBlockData476, orbitBlockData477, orbitBlockData478, orbitBlockData479]

theorem orbitChunk29_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 29 i) (orbitChunk29Data i) = true := by
  fin_cases i
  · exact orbitBlock464_checked
  · exact orbitBlock465_checked
  · exact orbitBlock466_checked
  · exact orbitBlock467_checked
  · exact orbitBlock468_checked
  · exact orbitBlock469_checked
  · exact orbitBlock470_checked
  · exact orbitBlock471_checked
  · exact orbitBlock472_checked
  · exact orbitBlock473_checked
  · exact orbitBlock474_checked
  · exact orbitBlock475_checked
  · exact orbitBlock476_checked
  · exact orbitBlock477_checked
  · exact orbitBlock478_checked
  · exact orbitBlock479_checked

def orbitChunk30Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData480, orbitBlockData481, orbitBlockData482, orbitBlockData483, orbitBlockData484, orbitBlockData485, orbitBlockData486, orbitBlockData487, orbitBlockData488, orbitBlockData489, orbitBlockData490, orbitBlockData491, orbitBlockData492, orbitBlockData493, orbitBlockData494, orbitBlockData495]

theorem orbitChunk30_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 30 i) (orbitChunk30Data i) = true := by
  fin_cases i
  · exact orbitBlock480_checked
  · exact orbitBlock481_checked
  · exact orbitBlock482_checked
  · exact orbitBlock483_checked
  · exact orbitBlock484_checked
  · exact orbitBlock485_checked
  · exact orbitBlock486_checked
  · exact orbitBlock487_checked
  · exact orbitBlock488_checked
  · exact orbitBlock489_checked
  · exact orbitBlock490_checked
  · exact orbitBlock491_checked
  · exact orbitBlock492_checked
  · exact orbitBlock493_checked
  · exact orbitBlock494_checked
  · exact orbitBlock495_checked

def orbitChunk31Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData496, orbitBlockData497, orbitBlockData498, orbitBlockData499, orbitBlockData500, orbitBlockData501, orbitBlockData502, orbitBlockData503, orbitBlockData504, orbitBlockData505, orbitBlockData506, orbitBlockData507, orbitBlockData508, orbitBlockData509, orbitBlockData510, orbitBlockData511]

theorem orbitChunk31_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 31 i) (orbitChunk31Data i) = true := by
  fin_cases i
  · exact orbitBlock496_checked
  · exact orbitBlock497_checked
  · exact orbitBlock498_checked
  · exact orbitBlock499_checked
  · exact orbitBlock500_checked
  · exact orbitBlock501_checked
  · exact orbitBlock502_checked
  · exact orbitBlock503_checked
  · exact orbitBlock504_checked
  · exact orbitBlock505_checked
  · exact orbitBlock506_checked
  · exact orbitBlock507_checked
  · exact orbitBlock508_checked
  · exact orbitBlock509_checked
  · exact orbitBlock510_checked
  · exact orbitBlock511_checked

def orbitChunk32Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData512, orbitBlockData513, orbitBlockData514, orbitBlockData515, orbitBlockData516, orbitBlockData517, orbitBlockData518, orbitBlockData519, orbitBlockData520, orbitBlockData521, orbitBlockData522, orbitBlockData523, orbitBlockData524, orbitBlockData525, orbitBlockData526, orbitBlockData527]

theorem orbitChunk32_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 32 i) (orbitChunk32Data i) = true := by
  fin_cases i
  · exact orbitBlock512_checked
  · exact orbitBlock513_checked
  · exact orbitBlock514_checked
  · exact orbitBlock515_checked
  · exact orbitBlock516_checked
  · exact orbitBlock517_checked
  · exact orbitBlock518_checked
  · exact orbitBlock519_checked
  · exact orbitBlock520_checked
  · exact orbitBlock521_checked
  · exact orbitBlock522_checked
  · exact orbitBlock523_checked
  · exact orbitBlock524_checked
  · exact orbitBlock525_checked
  · exact orbitBlock526_checked
  · exact orbitBlock527_checked

def orbitChunk33Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData528, orbitBlockData529, orbitBlockData530, orbitBlockData531, orbitBlockData532, orbitBlockData533, orbitBlockData534, orbitBlockData535, orbitBlockData536, orbitBlockData537, orbitBlockData538, orbitBlockData539, orbitBlockData540, orbitBlockData541, orbitBlockData542, orbitBlockData543]

theorem orbitChunk33_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 33 i) (orbitChunk33Data i) = true := by
  fin_cases i
  · exact orbitBlock528_checked
  · exact orbitBlock529_checked
  · exact orbitBlock530_checked
  · exact orbitBlock531_checked
  · exact orbitBlock532_checked
  · exact orbitBlock533_checked
  · exact orbitBlock534_checked
  · exact orbitBlock535_checked
  · exact orbitBlock536_checked
  · exact orbitBlock537_checked
  · exact orbitBlock538_checked
  · exact orbitBlock539_checked
  · exact orbitBlock540_checked
  · exact orbitBlock541_checked
  · exact orbitBlock542_checked
  · exact orbitBlock543_checked

def orbitChunk34Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData544, orbitBlockData545, orbitBlockData546, orbitBlockData547, orbitBlockData548, orbitBlockData549, orbitBlockData550, orbitBlockData551, orbitBlockData552, orbitBlockData553, orbitBlockData554, orbitBlockData555, orbitBlockData556, orbitBlockData557, orbitBlockData558, orbitBlockData559]

theorem orbitChunk34_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 34 i) (orbitChunk34Data i) = true := by
  fin_cases i
  · exact orbitBlock544_checked
  · exact orbitBlock545_checked
  · exact orbitBlock546_checked
  · exact orbitBlock547_checked
  · exact orbitBlock548_checked
  · exact orbitBlock549_checked
  · exact orbitBlock550_checked
  · exact orbitBlock551_checked
  · exact orbitBlock552_checked
  · exact orbitBlock553_checked
  · exact orbitBlock554_checked
  · exact orbitBlock555_checked
  · exact orbitBlock556_checked
  · exact orbitBlock557_checked
  · exact orbitBlock558_checked
  · exact orbitBlock559_checked

def orbitChunk35Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData560, orbitBlockData561, orbitBlockData562, orbitBlockData563, orbitBlockData564, orbitBlockData565, orbitBlockData566, orbitBlockData567, orbitBlockData568, orbitBlockData569, orbitBlockData570, orbitBlockData571, orbitBlockData572, orbitBlockData573, orbitBlockData574, orbitBlockData575]

theorem orbitChunk35_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 35 i) (orbitChunk35Data i) = true := by
  fin_cases i
  · exact orbitBlock560_checked
  · exact orbitBlock561_checked
  · exact orbitBlock562_checked
  · exact orbitBlock563_checked
  · exact orbitBlock564_checked
  · exact orbitBlock565_checked
  · exact orbitBlock566_checked
  · exact orbitBlock567_checked
  · exact orbitBlock568_checked
  · exact orbitBlock569_checked
  · exact orbitBlock570_checked
  · exact orbitBlock571_checked
  · exact orbitBlock572_checked
  · exact orbitBlock573_checked
  · exact orbitBlock574_checked
  · exact orbitBlock575_checked

def orbitChunk36Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData576, orbitBlockData577, orbitBlockData578, orbitBlockData579, orbitBlockData580, orbitBlockData581, orbitBlockData582, orbitBlockData583, orbitBlockData584, orbitBlockData585, orbitBlockData586, orbitBlockData587, orbitBlockData588, orbitBlockData589, orbitBlockData590, orbitBlockData591]

theorem orbitChunk36_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 36 i) (orbitChunk36Data i) = true := by
  fin_cases i
  · exact orbitBlock576_checked
  · exact orbitBlock577_checked
  · exact orbitBlock578_checked
  · exact orbitBlock579_checked
  · exact orbitBlock580_checked
  · exact orbitBlock581_checked
  · exact orbitBlock582_checked
  · exact orbitBlock583_checked
  · exact orbitBlock584_checked
  · exact orbitBlock585_checked
  · exact orbitBlock586_checked
  · exact orbitBlock587_checked
  · exact orbitBlock588_checked
  · exact orbitBlock589_checked
  · exact orbitBlock590_checked
  · exact orbitBlock591_checked

def orbitChunk37Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData592, orbitBlockData593, orbitBlockData594, orbitBlockData595, orbitBlockData596, orbitBlockData597, orbitBlockData598, orbitBlockData599, orbitBlockData600, orbitBlockData601, orbitBlockData602, orbitBlockData603, orbitBlockData604, orbitBlockData605, orbitBlockData606, orbitBlockData607]

theorem orbitChunk37_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 37 i) (orbitChunk37Data i) = true := by
  fin_cases i
  · exact orbitBlock592_checked
  · exact orbitBlock593_checked
  · exact orbitBlock594_checked
  · exact orbitBlock595_checked
  · exact orbitBlock596_checked
  · exact orbitBlock597_checked
  · exact orbitBlock598_checked
  · exact orbitBlock599_checked
  · exact orbitBlock600_checked
  · exact orbitBlock601_checked
  · exact orbitBlock602_checked
  · exact orbitBlock603_checked
  · exact orbitBlock604_checked
  · exact orbitBlock605_checked
  · exact orbitBlock606_checked
  · exact orbitBlock607_checked

def orbitChunk38Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData608, orbitBlockData609, orbitBlockData610, orbitBlockData611, orbitBlockData612, orbitBlockData613, orbitBlockData614, orbitBlockData615, orbitBlockData616, orbitBlockData617, orbitBlockData618, orbitBlockData619, orbitBlockData620, orbitBlockData621, orbitBlockData622, orbitBlockData623]

theorem orbitChunk38_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 38 i) (orbitChunk38Data i) = true := by
  fin_cases i
  · exact orbitBlock608_checked
  · exact orbitBlock609_checked
  · exact orbitBlock610_checked
  · exact orbitBlock611_checked
  · exact orbitBlock612_checked
  · exact orbitBlock613_checked
  · exact orbitBlock614_checked
  · exact orbitBlock615_checked
  · exact orbitBlock616_checked
  · exact orbitBlock617_checked
  · exact orbitBlock618_checked
  · exact orbitBlock619_checked
  · exact orbitBlock620_checked
  · exact orbitBlock621_checked
  · exact orbitBlock622_checked
  · exact orbitBlock623_checked

def orbitChunk39Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData624, orbitBlockData625, orbitBlockData626, orbitBlockData627, orbitBlockData628, orbitBlockData629, orbitBlockData630, orbitBlockData631, orbitBlockData632, orbitBlockData633, orbitBlockData634, orbitBlockData635, orbitBlockData636, orbitBlockData637, orbitBlockData638, orbitBlockData639]

theorem orbitChunk39_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 39 i) (orbitChunk39Data i) = true := by
  fin_cases i
  · exact orbitBlock624_checked
  · exact orbitBlock625_checked
  · exact orbitBlock626_checked
  · exact orbitBlock627_checked
  · exact orbitBlock628_checked
  · exact orbitBlock629_checked
  · exact orbitBlock630_checked
  · exact orbitBlock631_checked
  · exact orbitBlock632_checked
  · exact orbitBlock633_checked
  · exact orbitBlock634_checked
  · exact orbitBlock635_checked
  · exact orbitBlock636_checked
  · exact orbitBlock637_checked
  · exact orbitBlock638_checked
  · exact orbitBlock639_checked

def orbitChunk40Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData640, orbitBlockData641, orbitBlockData642, orbitBlockData643, orbitBlockData644, orbitBlockData645, orbitBlockData646, orbitBlockData647, orbitBlockData648, orbitBlockData649, orbitBlockData650, orbitBlockData651, orbitBlockData652, orbitBlockData653, orbitBlockData654, orbitBlockData655]

theorem orbitChunk40_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 40 i) (orbitChunk40Data i) = true := by
  fin_cases i
  · exact orbitBlock640_checked
  · exact orbitBlock641_checked
  · exact orbitBlock642_checked
  · exact orbitBlock643_checked
  · exact orbitBlock644_checked
  · exact orbitBlock645_checked
  · exact orbitBlock646_checked
  · exact orbitBlock647_checked
  · exact orbitBlock648_checked
  · exact orbitBlock649_checked
  · exact orbitBlock650_checked
  · exact orbitBlock651_checked
  · exact orbitBlock652_checked
  · exact orbitBlock653_checked
  · exact orbitBlock654_checked
  · exact orbitBlock655_checked

def orbitChunk41Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData656, orbitBlockData657, orbitBlockData658, orbitBlockData659, orbitBlockData660, orbitBlockData661, orbitBlockData662, orbitBlockData663, orbitBlockData664, orbitBlockData665, orbitBlockData666, orbitBlockData667, orbitBlockData668, orbitBlockData669, orbitBlockData670, orbitBlockData671]

theorem orbitChunk41_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 41 i) (orbitChunk41Data i) = true := by
  fin_cases i
  · exact orbitBlock656_checked
  · exact orbitBlock657_checked
  · exact orbitBlock658_checked
  · exact orbitBlock659_checked
  · exact orbitBlock660_checked
  · exact orbitBlock661_checked
  · exact orbitBlock662_checked
  · exact orbitBlock663_checked
  · exact orbitBlock664_checked
  · exact orbitBlock665_checked
  · exact orbitBlock666_checked
  · exact orbitBlock667_checked
  · exact orbitBlock668_checked
  · exact orbitBlock669_checked
  · exact orbitBlock670_checked
  · exact orbitBlock671_checked

def orbitChunk42Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData672, orbitBlockData673, orbitBlockData674, orbitBlockData675, orbitBlockData676, orbitBlockData677, orbitBlockData678, orbitBlockData679, orbitBlockData680, orbitBlockData681, orbitBlockData682, orbitBlockData683, orbitBlockData684, orbitBlockData685, orbitBlockData686, orbitBlockData687]

theorem orbitChunk42_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 42 i) (orbitChunk42Data i) = true := by
  fin_cases i
  · exact orbitBlock672_checked
  · exact orbitBlock673_checked
  · exact orbitBlock674_checked
  · exact orbitBlock675_checked
  · exact orbitBlock676_checked
  · exact orbitBlock677_checked
  · exact orbitBlock678_checked
  · exact orbitBlock679_checked
  · exact orbitBlock680_checked
  · exact orbitBlock681_checked
  · exact orbitBlock682_checked
  · exact orbitBlock683_checked
  · exact orbitBlock684_checked
  · exact orbitBlock685_checked
  · exact orbitBlock686_checked
  · exact orbitBlock687_checked

def orbitChunk43Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData688, orbitBlockData689, orbitBlockData690, orbitBlockData691, orbitBlockData692, orbitBlockData693, orbitBlockData694, orbitBlockData695, orbitBlockData696, orbitBlockData697, orbitBlockData698, orbitBlockData699, orbitBlockData700, orbitBlockData701, orbitBlockData702, orbitBlockData703]

theorem orbitChunk43_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 43 i) (orbitChunk43Data i) = true := by
  fin_cases i
  · exact orbitBlock688_checked
  · exact orbitBlock689_checked
  · exact orbitBlock690_checked
  · exact orbitBlock691_checked
  · exact orbitBlock692_checked
  · exact orbitBlock693_checked
  · exact orbitBlock694_checked
  · exact orbitBlock695_checked
  · exact orbitBlock696_checked
  · exact orbitBlock697_checked
  · exact orbitBlock698_checked
  · exact orbitBlock699_checked
  · exact orbitBlock700_checked
  · exact orbitBlock701_checked
  · exact orbitBlock702_checked
  · exact orbitBlock703_checked

def orbitChunk44Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData704, orbitBlockData705, orbitBlockData706, orbitBlockData707, orbitBlockData708, orbitBlockData709, orbitBlockData710, orbitBlockData711, orbitBlockData712, orbitBlockData713, orbitBlockData714, orbitBlockData715, orbitBlockData716, orbitBlockData717, orbitBlockData718, orbitBlockData719]

theorem orbitChunk44_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 44 i) (orbitChunk44Data i) = true := by
  fin_cases i
  · exact orbitBlock704_checked
  · exact orbitBlock705_checked
  · exact orbitBlock706_checked
  · exact orbitBlock707_checked
  · exact orbitBlock708_checked
  · exact orbitBlock709_checked
  · exact orbitBlock710_checked
  · exact orbitBlock711_checked
  · exact orbitBlock712_checked
  · exact orbitBlock713_checked
  · exact orbitBlock714_checked
  · exact orbitBlock715_checked
  · exact orbitBlock716_checked
  · exact orbitBlock717_checked
  · exact orbitBlock718_checked
  · exact orbitBlock719_checked

def orbitChunk45Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData720, orbitBlockData721, orbitBlockData722, orbitBlockData723, orbitBlockData724, orbitBlockData725, orbitBlockData726, orbitBlockData727, orbitBlockData728, orbitBlockData729, orbitBlockData730, orbitBlockData731, orbitBlockData732, orbitBlockData733, orbitBlockData734, orbitBlockData735]

theorem orbitChunk45_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 45 i) (orbitChunk45Data i) = true := by
  fin_cases i
  · exact orbitBlock720_checked
  · exact orbitBlock721_checked
  · exact orbitBlock722_checked
  · exact orbitBlock723_checked
  · exact orbitBlock724_checked
  · exact orbitBlock725_checked
  · exact orbitBlock726_checked
  · exact orbitBlock727_checked
  · exact orbitBlock728_checked
  · exact orbitBlock729_checked
  · exact orbitBlock730_checked
  · exact orbitBlock731_checked
  · exact orbitBlock732_checked
  · exact orbitBlock733_checked
  · exact orbitBlock734_checked
  · exact orbitBlock735_checked

def orbitChunk46Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData736, orbitBlockData737, orbitBlockData738, orbitBlockData739, orbitBlockData740, orbitBlockData741, orbitBlockData742, orbitBlockData743, orbitBlockData744, orbitBlockData745, orbitBlockData746, orbitBlockData747, orbitBlockData748, orbitBlockData749, orbitBlockData750, orbitBlockData751]

theorem orbitChunk46_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 46 i) (orbitChunk46Data i) = true := by
  fin_cases i
  · exact orbitBlock736_checked
  · exact orbitBlock737_checked
  · exact orbitBlock738_checked
  · exact orbitBlock739_checked
  · exact orbitBlock740_checked
  · exact orbitBlock741_checked
  · exact orbitBlock742_checked
  · exact orbitBlock743_checked
  · exact orbitBlock744_checked
  · exact orbitBlock745_checked
  · exact orbitBlock746_checked
  · exact orbitBlock747_checked
  · exact orbitBlock748_checked
  · exact orbitBlock749_checked
  · exact orbitBlock750_checked
  · exact orbitBlock751_checked

def orbitChunk47Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData752, orbitBlockData753, orbitBlockData754, orbitBlockData755, orbitBlockData756, orbitBlockData757, orbitBlockData758, orbitBlockData759, orbitBlockData760, orbitBlockData761, orbitBlockData762, orbitBlockData763, orbitBlockData764, orbitBlockData765, orbitBlockData766, orbitBlockData767]

theorem orbitChunk47_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 47 i) (orbitChunk47Data i) = true := by
  fin_cases i
  · exact orbitBlock752_checked
  · exact orbitBlock753_checked
  · exact orbitBlock754_checked
  · exact orbitBlock755_checked
  · exact orbitBlock756_checked
  · exact orbitBlock757_checked
  · exact orbitBlock758_checked
  · exact orbitBlock759_checked
  · exact orbitBlock760_checked
  · exact orbitBlock761_checked
  · exact orbitBlock762_checked
  · exact orbitBlock763_checked
  · exact orbitBlock764_checked
  · exact orbitBlock765_checked
  · exact orbitBlock766_checked
  · exact orbitBlock767_checked

def orbitChunk48Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData768, orbitBlockData769, orbitBlockData770, orbitBlockData771, orbitBlockData772, orbitBlockData773, orbitBlockData774, orbitBlockData775, orbitBlockData776, orbitBlockData777, orbitBlockData778, orbitBlockData779, orbitBlockData780, orbitBlockData781, orbitBlockData782, orbitBlockData783]

theorem orbitChunk48_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 48 i) (orbitChunk48Data i) = true := by
  fin_cases i
  · exact orbitBlock768_checked
  · exact orbitBlock769_checked
  · exact orbitBlock770_checked
  · exact orbitBlock771_checked
  · exact orbitBlock772_checked
  · exact orbitBlock773_checked
  · exact orbitBlock774_checked
  · exact orbitBlock775_checked
  · exact orbitBlock776_checked
  · exact orbitBlock777_checked
  · exact orbitBlock778_checked
  · exact orbitBlock779_checked
  · exact orbitBlock780_checked
  · exact orbitBlock781_checked
  · exact orbitBlock782_checked
  · exact orbitBlock783_checked

def orbitChunk49Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData784, orbitBlockData785, orbitBlockData786, orbitBlockData787, orbitBlockData788, orbitBlockData789, orbitBlockData790, orbitBlockData791, orbitBlockData792, orbitBlockData793, orbitBlockData794, orbitBlockData795, orbitBlockData796, orbitBlockData797, orbitBlockData798, orbitBlockData799]

theorem orbitChunk49_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 49 i) (orbitChunk49Data i) = true := by
  fin_cases i
  · exact orbitBlock784_checked
  · exact orbitBlock785_checked
  · exact orbitBlock786_checked
  · exact orbitBlock787_checked
  · exact orbitBlock788_checked
  · exact orbitBlock789_checked
  · exact orbitBlock790_checked
  · exact orbitBlock791_checked
  · exact orbitBlock792_checked
  · exact orbitBlock793_checked
  · exact orbitBlock794_checked
  · exact orbitBlock795_checked
  · exact orbitBlock796_checked
  · exact orbitBlock797_checked
  · exact orbitBlock798_checked
  · exact orbitBlock799_checked

def orbitChunk50Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData800, orbitBlockData801, orbitBlockData802, orbitBlockData803, orbitBlockData804, orbitBlockData805, orbitBlockData806, orbitBlockData807, orbitBlockData808, orbitBlockData809, orbitBlockData810, orbitBlockData811, orbitBlockData812, orbitBlockData813, orbitBlockData814, orbitBlockData815]

theorem orbitChunk50_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 50 i) (orbitChunk50Data i) = true := by
  fin_cases i
  · exact orbitBlock800_checked
  · exact orbitBlock801_checked
  · exact orbitBlock802_checked
  · exact orbitBlock803_checked
  · exact orbitBlock804_checked
  · exact orbitBlock805_checked
  · exact orbitBlock806_checked
  · exact orbitBlock807_checked
  · exact orbitBlock808_checked
  · exact orbitBlock809_checked
  · exact orbitBlock810_checked
  · exact orbitBlock811_checked
  · exact orbitBlock812_checked
  · exact orbitBlock813_checked
  · exact orbitBlock814_checked
  · exact orbitBlock815_checked

def orbitChunk51Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData816, orbitBlockData817, orbitBlockData818, orbitBlockData819, orbitBlockData820, orbitBlockData821, orbitBlockData822, orbitBlockData823, orbitBlockData824, orbitBlockData825, orbitBlockData826, orbitBlockData827, orbitBlockData828, orbitBlockData829, orbitBlockData830, orbitBlockData831]

theorem orbitChunk51_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 51 i) (orbitChunk51Data i) = true := by
  fin_cases i
  · exact orbitBlock816_checked
  · exact orbitBlock817_checked
  · exact orbitBlock818_checked
  · exact orbitBlock819_checked
  · exact orbitBlock820_checked
  · exact orbitBlock821_checked
  · exact orbitBlock822_checked
  · exact orbitBlock823_checked
  · exact orbitBlock824_checked
  · exact orbitBlock825_checked
  · exact orbitBlock826_checked
  · exact orbitBlock827_checked
  · exact orbitBlock828_checked
  · exact orbitBlock829_checked
  · exact orbitBlock830_checked
  · exact orbitBlock831_checked

def orbitChunk52Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData832, orbitBlockData833, orbitBlockData834, orbitBlockData835, orbitBlockData836, orbitBlockData837, orbitBlockData838, orbitBlockData839, orbitBlockData840, orbitBlockData841, orbitBlockData842, orbitBlockData843, orbitBlockData844, orbitBlockData845, orbitBlockData846, orbitBlockData847]

theorem orbitChunk52_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 52 i) (orbitChunk52Data i) = true := by
  fin_cases i
  · exact orbitBlock832_checked
  · exact orbitBlock833_checked
  · exact orbitBlock834_checked
  · exact orbitBlock835_checked
  · exact orbitBlock836_checked
  · exact orbitBlock837_checked
  · exact orbitBlock838_checked
  · exact orbitBlock839_checked
  · exact orbitBlock840_checked
  · exact orbitBlock841_checked
  · exact orbitBlock842_checked
  · exact orbitBlock843_checked
  · exact orbitBlock844_checked
  · exact orbitBlock845_checked
  · exact orbitBlock846_checked
  · exact orbitBlock847_checked

def orbitChunk53Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData848, orbitBlockData849, orbitBlockData850, orbitBlockData851, orbitBlockData852, orbitBlockData853, orbitBlockData854, orbitBlockData855, orbitBlockData856, orbitBlockData857, orbitBlockData858, orbitBlockData859, orbitBlockData860, orbitBlockData861, orbitBlockData862, orbitBlockData863]

theorem orbitChunk53_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 53 i) (orbitChunk53Data i) = true := by
  fin_cases i
  · exact orbitBlock848_checked
  · exact orbitBlock849_checked
  · exact orbitBlock850_checked
  · exact orbitBlock851_checked
  · exact orbitBlock852_checked
  · exact orbitBlock853_checked
  · exact orbitBlock854_checked
  · exact orbitBlock855_checked
  · exact orbitBlock856_checked
  · exact orbitBlock857_checked
  · exact orbitBlock858_checked
  · exact orbitBlock859_checked
  · exact orbitBlock860_checked
  · exact orbitBlock861_checked
  · exact orbitBlock862_checked
  · exact orbitBlock863_checked

def orbitChunk54Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData864, orbitBlockData865, orbitBlockData866, orbitBlockData867, orbitBlockData868, orbitBlockData869, orbitBlockData870, orbitBlockData871, orbitBlockData872, orbitBlockData873, orbitBlockData874, orbitBlockData875, orbitBlockData876, orbitBlockData877, orbitBlockData878, orbitBlockData879]

theorem orbitChunk54_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 54 i) (orbitChunk54Data i) = true := by
  fin_cases i
  · exact orbitBlock864_checked
  · exact orbitBlock865_checked
  · exact orbitBlock866_checked
  · exact orbitBlock867_checked
  · exact orbitBlock868_checked
  · exact orbitBlock869_checked
  · exact orbitBlock870_checked
  · exact orbitBlock871_checked
  · exact orbitBlock872_checked
  · exact orbitBlock873_checked
  · exact orbitBlock874_checked
  · exact orbitBlock875_checked
  · exact orbitBlock876_checked
  · exact orbitBlock877_checked
  · exact orbitBlock878_checked
  · exact orbitBlock879_checked

def orbitChunk55Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData880, orbitBlockData881, orbitBlockData882, orbitBlockData883, orbitBlockData884, orbitBlockData885, orbitBlockData886, orbitBlockData887, orbitBlockData888, orbitBlockData889, orbitBlockData890, orbitBlockData891, orbitBlockData892, orbitBlockData893, orbitBlockData894, orbitBlockData895]

theorem orbitChunk55_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 55 i) (orbitChunk55Data i) = true := by
  fin_cases i
  · exact orbitBlock880_checked
  · exact orbitBlock881_checked
  · exact orbitBlock882_checked
  · exact orbitBlock883_checked
  · exact orbitBlock884_checked
  · exact orbitBlock885_checked
  · exact orbitBlock886_checked
  · exact orbitBlock887_checked
  · exact orbitBlock888_checked
  · exact orbitBlock889_checked
  · exact orbitBlock890_checked
  · exact orbitBlock891_checked
  · exact orbitBlock892_checked
  · exact orbitBlock893_checked
  · exact orbitBlock894_checked
  · exact orbitBlock895_checked

def orbitChunk56Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData896, orbitBlockData897, orbitBlockData898, orbitBlockData899, orbitBlockData900, orbitBlockData901, orbitBlockData902, orbitBlockData903, orbitBlockData904, orbitBlockData905, orbitBlockData906, orbitBlockData907, orbitBlockData908, orbitBlockData909, orbitBlockData910, orbitBlockData911]

theorem orbitChunk56_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 56 i) (orbitChunk56Data i) = true := by
  fin_cases i
  · exact orbitBlock896_checked
  · exact orbitBlock897_checked
  · exact orbitBlock898_checked
  · exact orbitBlock899_checked
  · exact orbitBlock900_checked
  · exact orbitBlock901_checked
  · exact orbitBlock902_checked
  · exact orbitBlock903_checked
  · exact orbitBlock904_checked
  · exact orbitBlock905_checked
  · exact orbitBlock906_checked
  · exact orbitBlock907_checked
  · exact orbitBlock908_checked
  · exact orbitBlock909_checked
  · exact orbitBlock910_checked
  · exact orbitBlock911_checked

def orbitChunk57Data : Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitBlockData912, orbitBlockData913, orbitBlockData914, orbitBlockData915, orbitBlockData916, orbitBlockData917, orbitBlockData918, orbitBlockData919, orbitBlockData000, orbitBlockData001, orbitBlockData002, orbitBlockData003, orbitBlockData004, orbitBlockData005, orbitBlockData006, orbitBlockData007]

theorem orbitChunk57_checked (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock 57 i) (orbitChunk57Data i) = true := by
  fin_cases i
  · exact orbitBlock912_checked
  · exact orbitBlock913_checked
  · exact orbitBlock914_checked
  · exact orbitBlock915_checked
  · exact orbitBlock916_checked
  · exact orbitBlock917_checked
  · exact orbitBlock918_checked
  · exact orbitBlock919_checked
  · exact orbitBlock000_checked
  · exact orbitBlock001_checked
  · exact orbitBlock002_checked
  · exact orbitBlock003_checked
  · exact orbitBlock004_checked
  · exact orbitBlock005_checked
  · exact orbitBlock006_checked
  · exact orbitBlock007_checked

def allOrbitChunkData : Fin 58 → Fin 16 → FiniteTable (Nat × Nat) :=
  ![orbitChunk00Data, orbitChunk01Data, orbitChunk02Data, orbitChunk03Data, orbitChunk04Data, orbitChunk05Data, orbitChunk06Data, orbitChunk07Data, orbitChunk08Data, orbitChunk09Data, orbitChunk10Data, orbitChunk11Data, orbitChunk12Data, orbitChunk13Data, orbitChunk14Data, orbitChunk15Data, orbitChunk16Data, orbitChunk17Data, orbitChunk18Data, orbitChunk19Data, orbitChunk20Data, orbitChunk21Data, orbitChunk22Data, orbitChunk23Data, orbitChunk24Data, orbitChunk25Data, orbitChunk26Data, orbitChunk27Data, orbitChunk28Data, orbitChunk29Data, orbitChunk30Data, orbitChunk31Data, orbitChunk32Data, orbitChunk33Data, orbitChunk34Data, orbitChunk35Data, orbitChunk36Data, orbitChunk37Data, orbitChunk38Data, orbitChunk39Data, orbitChunk40Data, orbitChunk41Data, orbitChunk42Data, orbitChunk43Data, orbitChunk44Data, orbitChunk45Data, orbitChunk46Data, orbitChunk47Data, orbitChunk48Data, orbitChunk49Data, orbitChunk50Data, orbitChunk51Data, orbitChunk52Data, orbitChunk53Data, orbitChunk54Data, orbitChunk55Data, orbitChunk56Data, orbitChunk57Data]

theorem allOrbitChunks_checked (c : Fin 58) (i : Fin 16) :
    orbitBlockCheck (chunkSourceBlock c i) (allOrbitChunkData c i) = true := by
  fin_cases c
  · exact orbitChunk00_checked i
  · exact orbitChunk01_checked i
  · exact orbitChunk02_checked i
  · exact orbitChunk03_checked i
  · exact orbitChunk04_checked i
  · exact orbitChunk05_checked i
  · exact orbitChunk06_checked i
  · exact orbitChunk07_checked i
  · exact orbitChunk08_checked i
  · exact orbitChunk09_checked i
  · exact orbitChunk10_checked i
  · exact orbitChunk11_checked i
  · exact orbitChunk12_checked i
  · exact orbitChunk13_checked i
  · exact orbitChunk14_checked i
  · exact orbitChunk15_checked i
  · exact orbitChunk16_checked i
  · exact orbitChunk17_checked i
  · exact orbitChunk18_checked i
  · exact orbitChunk19_checked i
  · exact orbitChunk20_checked i
  · exact orbitChunk21_checked i
  · exact orbitChunk22_checked i
  · exact orbitChunk23_checked i
  · exact orbitChunk24_checked i
  · exact orbitChunk25_checked i
  · exact orbitChunk26_checked i
  · exact orbitChunk27_checked i
  · exact orbitChunk28_checked i
  · exact orbitChunk29_checked i
  · exact orbitChunk30_checked i
  · exact orbitChunk31_checked i
  · exact orbitChunk32_checked i
  · exact orbitChunk33_checked i
  · exact orbitChunk34_checked i
  · exact orbitChunk35_checked i
  · exact orbitChunk36_checked i
  · exact orbitChunk37_checked i
  · exact orbitChunk38_checked i
  · exact orbitChunk39_checked i
  · exact orbitChunk40_checked i
  · exact orbitChunk41_checked i
  · exact orbitChunk42_checked i
  · exact orbitChunk43_checked i
  · exact orbitChunk44_checked i
  · exact orbitChunk45_checked i
  · exact orbitChunk46_checked i
  · exact orbitChunk47_checked i
  · exact orbitChunk48_checked i
  · exact orbitChunk49_checked i
  · exact orbitChunk50_checked i
  · exact orbitChunk51_checked i
  · exact orbitChunk52_checked i
  · exact orbitChunk53_checked i
  · exact orbitChunk54_checked i
  · exact orbitChunk55_checked i
  · exact orbitChunk56_checked i
  · exact orbitChunk57_checked i

def blockChunk (b : Fin 920) : Fin 58 := ⟨b.val/16,by have := b.isLt; omega⟩
def blockOffset (b : Fin 920) : Fin 16 := ⟨b.val%16,Nat.mod_lt _ (by decide)⟩

theorem chunkSourceBlock_decompose (b : Fin 920) :
    chunkSourceBlock (blockChunk b) (blockOffset b) = b := by
  apply Fin.ext
  change (16*(b.val/16)+b.val%16)%920 = b.val
  have he : 16*(b.val/16)+b.val%16 = b.val := by omega
  rw [he,Nat.mod_eq_of_lt b.isLt]

def allOrbitBlockData (b : Fin 920) : FiniteTable (Nat × Nat) :=
  allOrbitChunkData (blockChunk b) (blockOffset b)

theorem allOrbitBlocks_checked (b : Fin 920) : orbitBlockCheck b (allOrbitBlockData b) = true := by
  have hh := allOrbitChunks_checked (blockChunk b) (blockOffset b)
  rw [chunkSourceBlock_decompose] at hh
  exact hh

theorem solved_of_all_representatives
    (h : ∀ i : Fin 4045, Solved (stateEquiv (representativeCode i))) :
    ∀ state : DirectionTriple, Solved state :=
  all_solved_of_orbit_blocks allOrbitBlockData allOrbitBlocks_checked h

end
end Holant.Pauli.ExoticKlein.SixPort

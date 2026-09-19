import R5Kernel.Probes.S11C11CanonicalDefinitions
import R5Kernel.Audit

set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000

namespace Erdos1011

def kernelC11CycleTypeMasks : List ℕ :=
  [1, 2, 4, 5, 8, 9, 10, 16, 17, 18, 20, 21, 32, 33, 34, 36, 37, 40, 41, 42,
   64, 65, 66, 68, 69, 72, 73, 74, 80, 81, 82, 84, 85, 128, 129, 130, 132,
   133, 136, 137, 138, 144, 145, 146, 148, 149, 160, 161, 162, 164, 165,
   168, 169, 170, 256, 257, 258, 260, 261, 264, 265, 266, 272, 273, 274,
   276, 277, 288, 289, 290, 292, 293, 296, 297, 298, 320, 321, 322, 324,
   325, 328, 329, 330, 336, 337, 338, 340, 341, 512, 513, 514, 516, 517,
   520, 521, 522, 528, 529, 530, 532, 533, 544, 545, 546, 548, 549, 552,
   553, 554, 576, 577, 578, 580, 581, 584, 585, 586, 592, 593, 594, 596,
   597, 640, 641, 642, 644, 645, 648, 649, 650, 656, 657, 658, 660, 661,
   672, 673, 674, 676, 677, 680, 681, 682, 1024, 1026, 1028, 1032, 1034,
   1040, 1042, 1044, 1056, 1058, 1060, 1064, 1066, 1088, 1090, 1092, 1096,
   1098, 1104, 1106, 1108, 1152, 1154, 1156, 1160, 1162, 1168, 1170, 1172,
   1184, 1186, 1188, 1192, 1194, 1280, 1282, 1284, 1288, 1290, 1296, 1298,
   1300, 1312, 1314, 1316, 1320, 1322, 1344, 1346, 1348, 1352, 1354, 1360,
   1362, 1364]

def kernelC11CycleTypeAt (i : Fin 198) : Finset (Fin 11) :=
  kernelC11SmallMask (kernelC11CycleTypeMasks.getD i.val 0)

theorem kernel_c11_cycle_type_masks_length : kernelC11CycleTypeMasks.length = 198 := by
  decide

theorem kernel_c11_cycle_types_eq_image :
    cycleTypes 11 11 =
      (Finset.univ : Finset (Fin 198)).image kernelC11CycleTypeAt := by
  decide +kernel

run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_cycle_type_masks_length
run_cmd R5Kernel.checkStandardAxioms ``kernel_c11_cycle_types_eq_image

end Erdos1011

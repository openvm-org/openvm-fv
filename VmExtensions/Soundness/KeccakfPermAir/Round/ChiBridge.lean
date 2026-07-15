import VmExtensions.Soundness.KeccakfPermAir.Round.ChiHelpers
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 4000000
namespace KeccakfPermAir.Soundness
open BabyBear KeccakfPermAir.constraints
variable {ExtF : Type} [Field ExtF]
  {air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF} {row : ℕ}

/-- Opaque (`def`, not `abbrev`) wrapper for the `chiCanonicalK` chi-recomposition
    Prop, used to keep the `Fin 100` dependent matcher in `chi_canonical_of_chi`
    small (see below).  Definitionally `chiCanonicalK`, so callers still receive
    `chiCanonicalK air n.val row`. -/
def chiCanonicalKProp
    (air : KeccakfPermAir.Valid_KeccakfPermAir FBB ExtF) (n row : ℕ) : Prop :=
  chiCanonicalK air n row

/-! ## Per-constraint chi Horner-peeling lemmas

The openvm v2.0.0 extraction emits each chi output limb constraint
(`constraint_2910..3009`) as a nested Horner accumulator chain of `inter_*`
definitions, NOT as a form definitionally equal to `chiCanonicalK`.  Proving the
`ChiConstraints` field directly against `chiCanonicalK` by `rfl`/defeq is
catastrophic (a single bridge times out at `whnf`).  Each `peel_chi_<cnum>`
instead keeps the accumulators opaque and telescopes the Horner recursion one
level at a time — `inter = ch(a,b,d) + 2 * inter_next`, with the chi bit
`ch(a,b,d) = a + d - b·d - 2ad + 2abd = fieldXor((1-b)·d, a)` — abstracting the
columns to an opaque `mc` so the `ring` steps never unfold the concrete `Circuit`
instance dictionary. -/

private theorem peel_chi_2910 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2910 c row) :
    ((mc 865 + mc 1654 - mc 1269*mc 1654 - 2*mc 865*mc 1654 + 2*mc 865*mc 1269*mc 1654) + 2*(mc 866 + mc 1655 - mc 1270*mc 1655 - 2*mc 866*mc 1655 + 2*mc 866*mc 1270*mc 1655) + 4*(mc 867 + mc 1656 - mc 1271*mc 1656 - 2*mc 867*mc 1656 + 2*mc 867*mc 1271*mc 1656) + 8*(mc 868 + mc 1657 - mc 1272*mc 1657 - 2*mc 868*mc 1657 + 2*mc 868*mc 1272*mc 1657) + 16*(mc 869 + mc 1658 - mc 1273*mc 1658 - 2*mc 869*mc 1658 + 2*mc 869*mc 1273*mc 1658) + 32*(mc 870 + mc 1659 - mc 1274*mc 1659 - 2*mc 870*mc 1659 + 2*mc 870*mc 1274*mc 1659) + 64*(mc 871 + mc 1660 - mc 1275*mc 1660 - 2*mc 871*mc 1660 + 2*mc 871*mc 1275*mc 1660) + 128*(mc 872 + mc 1661 - mc 1276*mc 1661 - 2*mc 872*mc 1661 + 2*mc 872*mc 1276*mc 1661) + 256*(mc 873 + mc 1662 - mc 1277*mc 1662 - 2*mc 873*mc 1662 + 2*mc 873*mc 1277*mc 1662) + 512*(mc 874 + mc 1663 - mc 1278*mc 1663 - 2*mc 874*mc 1663 + 2*mc 874*mc 1278*mc 1663) + 1024*(mc 875 + mc 1664 - mc 1279*mc 1664 - 2*mc 875*mc 1664 + 2*mc 875*mc 1279*mc 1664) + 2048*(mc 876 + mc 1665 - mc 1280*mc 1665 - 2*mc 876*mc 1665 + 2*mc 876*mc 1280*mc 1665) + 4096*(mc 877 + mc 1666 - mc 1281*mc 1666 - 2*mc 877*mc 1666 + 2*mc 877*mc 1281*mc 1666) + 8192*(mc 878 + mc 1667 - mc 1282*mc 1667 - 2*mc 878*mc 1667 + 2*mc 878*mc 1282*mc 1667) + 16384*(mc 879 + mc 1668 - mc 1283*mc 1668 - 2*mc 879*mc 1668 + 2*mc 879*mc 1283*mc 1668) + 32768*(mc 880 + mc 1669 - mc 1284*mc 1669 - 2*mc 880*mc 1669 + 2*mc 880*mc 1284*mc 1669)) - mc 2465 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2910, KeccakfPermAir.extraction.inter_3770, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3769 c row = (mc 866 + mc 1655 - mc 1270*mc 1655 - 2*mc 866*mc 1655 + 2*mc 866*mc 1270*mc 1655) + 2 * KeccakfPermAir.extraction.inter_3767 c row := by
    simp only [KeccakfPermAir.extraction.inter_3769, KeccakfPermAir.extraction.inter_3768, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3767 c row = (mc 867 + mc 1656 - mc 1271*mc 1656 - 2*mc 867*mc 1656 + 2*mc 867*mc 1271*mc 1656) + 2 * KeccakfPermAir.extraction.inter_3765 c row := by
    simp only [KeccakfPermAir.extraction.inter_3767, KeccakfPermAir.extraction.inter_3766, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3765 c row = (mc 868 + mc 1657 - mc 1272*mc 1657 - 2*mc 868*mc 1657 + 2*mc 868*mc 1272*mc 1657) + 2 * KeccakfPermAir.extraction.inter_3763 c row := by
    simp only [KeccakfPermAir.extraction.inter_3765, KeccakfPermAir.extraction.inter_3764, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3763 c row = (mc 869 + mc 1658 - mc 1273*mc 1658 - 2*mc 869*mc 1658 + 2*mc 869*mc 1273*mc 1658) + 2 * KeccakfPermAir.extraction.inter_3761 c row := by
    simp only [KeccakfPermAir.extraction.inter_3763, KeccakfPermAir.extraction.inter_3762, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3761 c row = (mc 870 + mc 1659 - mc 1274*mc 1659 - 2*mc 870*mc 1659 + 2*mc 870*mc 1274*mc 1659) + 2 * KeccakfPermAir.extraction.inter_3759 c row := by
    simp only [KeccakfPermAir.extraction.inter_3761, KeccakfPermAir.extraction.inter_3760, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3759 c row = (mc 871 + mc 1660 - mc 1275*mc 1660 - 2*mc 871*mc 1660 + 2*mc 871*mc 1275*mc 1660) + 2 * KeccakfPermAir.extraction.inter_3757 c row := by
    simp only [KeccakfPermAir.extraction.inter_3759, KeccakfPermAir.extraction.inter_3758, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3757 c row = (mc 872 + mc 1661 - mc 1276*mc 1661 - 2*mc 872*mc 1661 + 2*mc 872*mc 1276*mc 1661) + 2 * KeccakfPermAir.extraction.inter_3755 c row := by
    simp only [KeccakfPermAir.extraction.inter_3757, KeccakfPermAir.extraction.inter_3756, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3755 c row = (mc 873 + mc 1662 - mc 1277*mc 1662 - 2*mc 873*mc 1662 + 2*mc 873*mc 1277*mc 1662) + 2 * KeccakfPermAir.extraction.inter_3753 c row := by
    simp only [KeccakfPermAir.extraction.inter_3755, KeccakfPermAir.extraction.inter_3754, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3753 c row = (mc 874 + mc 1663 - mc 1278*mc 1663 - 2*mc 874*mc 1663 + 2*mc 874*mc 1278*mc 1663) + 2 * KeccakfPermAir.extraction.inter_3751 c row := by
    simp only [KeccakfPermAir.extraction.inter_3753, KeccakfPermAir.extraction.inter_3752, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3751 c row = (mc 875 + mc 1664 - mc 1279*mc 1664 - 2*mc 875*mc 1664 + 2*mc 875*mc 1279*mc 1664) + 2 * KeccakfPermAir.extraction.inter_3749 c row := by
    simp only [KeccakfPermAir.extraction.inter_3751, KeccakfPermAir.extraction.inter_3750, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3749 c row = (mc 876 + mc 1665 - mc 1280*mc 1665 - 2*mc 876*mc 1665 + 2*mc 876*mc 1280*mc 1665) + 2 * KeccakfPermAir.extraction.inter_3747 c row := by
    simp only [KeccakfPermAir.extraction.inter_3749, KeccakfPermAir.extraction.inter_3748, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3747 c row = (mc 877 + mc 1666 - mc 1281*mc 1666 - 2*mc 877*mc 1666 + 2*mc 877*mc 1281*mc 1666) + 2 * KeccakfPermAir.extraction.inter_3745 c row := by
    simp only [KeccakfPermAir.extraction.inter_3747, KeccakfPermAir.extraction.inter_3746, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3745 c row = (mc 878 + mc 1667 - mc 1282*mc 1667 - 2*mc 878*mc 1667 + 2*mc 878*mc 1282*mc 1667) + 2 * KeccakfPermAir.extraction.inter_3743 c row := by
    simp only [KeccakfPermAir.extraction.inter_3745, KeccakfPermAir.extraction.inter_3744, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3743 c row = (mc 879 + mc 1668 - mc 1283*mc 1668 - 2*mc 879*mc 1668 + 2*mc 879*mc 1283*mc 1668) + 2 * KeccakfPermAir.extraction.inter_3741 c row := by
    simp only [KeccakfPermAir.extraction.inter_3743, KeccakfPermAir.extraction.inter_3742, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3741 c row = (mc 880 + mc 1669 - mc 1284*mc 1669 - 2*mc 880*mc 1669 + 2*mc 880*mc 1284*mc 1669) := by
    simp only [KeccakfPermAir.extraction.inter_3741, KeccakfPermAir.extraction.inter_3740, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2911 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2911 c row) :
    ((mc 881 + mc 1670 - mc 1285*mc 1670 - 2*mc 881*mc 1670 + 2*mc 881*mc 1285*mc 1670) + 2*(mc 882 + mc 1671 - mc 1286*mc 1671 - 2*mc 882*mc 1671 + 2*mc 882*mc 1286*mc 1671) + 4*(mc 883 + mc 1672 - mc 1287*mc 1672 - 2*mc 883*mc 1672 + 2*mc 883*mc 1287*mc 1672) + 8*(mc 884 + mc 1673 - mc 1288*mc 1673 - 2*mc 884*mc 1673 + 2*mc 884*mc 1288*mc 1673) + 16*(mc 885 + mc 1674 - mc 1289*mc 1674 - 2*mc 885*mc 1674 + 2*mc 885*mc 1289*mc 1674) + 32*(mc 886 + mc 1675 - mc 1290*mc 1675 - 2*mc 886*mc 1675 + 2*mc 886*mc 1290*mc 1675) + 64*(mc 887 + mc 1676 - mc 1291*mc 1676 - 2*mc 887*mc 1676 + 2*mc 887*mc 1291*mc 1676) + 128*(mc 888 + mc 1677 - mc 1292*mc 1677 - 2*mc 888*mc 1677 + 2*mc 888*mc 1292*mc 1677) + 256*(mc 889 + mc 1678 - mc 1293*mc 1678 - 2*mc 889*mc 1678 + 2*mc 889*mc 1293*mc 1678) + 512*(mc 890 + mc 1679 - mc 1294*mc 1679 - 2*mc 890*mc 1679 + 2*mc 890*mc 1294*mc 1679) + 1024*(mc 891 + mc 1680 - mc 1295*mc 1680 - 2*mc 891*mc 1680 + 2*mc 891*mc 1295*mc 1680) + 2048*(mc 892 + mc 1681 - mc 1296*mc 1681 - 2*mc 892*mc 1681 + 2*mc 892*mc 1296*mc 1681) + 4096*(mc 893 + mc 1682 - mc 1297*mc 1682 - 2*mc 893*mc 1682 + 2*mc 893*mc 1297*mc 1682) + 8192*(mc 894 + mc 1683 - mc 1298*mc 1683 - 2*mc 894*mc 1683 + 2*mc 894*mc 1298*mc 1683) + 16384*(mc 895 + mc 1684 - mc 1299*mc 1684 - 2*mc 895*mc 1684 + 2*mc 895*mc 1299*mc 1684) + 32768*(mc 896 + mc 1685 - mc 1300*mc 1685 - 2*mc 896*mc 1685 + 2*mc 896*mc 1300*mc 1685)) - mc 2466 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2911, KeccakfPermAir.extraction.inter_3801, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3800 c row = (mc 882 + mc 1671 - mc 1286*mc 1671 - 2*mc 882*mc 1671 + 2*mc 882*mc 1286*mc 1671) + 2 * KeccakfPermAir.extraction.inter_3798 c row := by
    simp only [KeccakfPermAir.extraction.inter_3800, KeccakfPermAir.extraction.inter_3799, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3798 c row = (mc 883 + mc 1672 - mc 1287*mc 1672 - 2*mc 883*mc 1672 + 2*mc 883*mc 1287*mc 1672) + 2 * KeccakfPermAir.extraction.inter_3796 c row := by
    simp only [KeccakfPermAir.extraction.inter_3798, KeccakfPermAir.extraction.inter_3797, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3796 c row = (mc 884 + mc 1673 - mc 1288*mc 1673 - 2*mc 884*mc 1673 + 2*mc 884*mc 1288*mc 1673) + 2 * KeccakfPermAir.extraction.inter_3794 c row := by
    simp only [KeccakfPermAir.extraction.inter_3796, KeccakfPermAir.extraction.inter_3795, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3794 c row = (mc 885 + mc 1674 - mc 1289*mc 1674 - 2*mc 885*mc 1674 + 2*mc 885*mc 1289*mc 1674) + 2 * KeccakfPermAir.extraction.inter_3792 c row := by
    simp only [KeccakfPermAir.extraction.inter_3794, KeccakfPermAir.extraction.inter_3793, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3792 c row = (mc 886 + mc 1675 - mc 1290*mc 1675 - 2*mc 886*mc 1675 + 2*mc 886*mc 1290*mc 1675) + 2 * KeccakfPermAir.extraction.inter_3790 c row := by
    simp only [KeccakfPermAir.extraction.inter_3792, KeccakfPermAir.extraction.inter_3791, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3790 c row = (mc 887 + mc 1676 - mc 1291*mc 1676 - 2*mc 887*mc 1676 + 2*mc 887*mc 1291*mc 1676) + 2 * KeccakfPermAir.extraction.inter_3788 c row := by
    simp only [KeccakfPermAir.extraction.inter_3790, KeccakfPermAir.extraction.inter_3789, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3788 c row = (mc 888 + mc 1677 - mc 1292*mc 1677 - 2*mc 888*mc 1677 + 2*mc 888*mc 1292*mc 1677) + 2 * KeccakfPermAir.extraction.inter_3786 c row := by
    simp only [KeccakfPermAir.extraction.inter_3788, KeccakfPermAir.extraction.inter_3787, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3786 c row = (mc 889 + mc 1678 - mc 1293*mc 1678 - 2*mc 889*mc 1678 + 2*mc 889*mc 1293*mc 1678) + 2 * KeccakfPermAir.extraction.inter_3784 c row := by
    simp only [KeccakfPermAir.extraction.inter_3786, KeccakfPermAir.extraction.inter_3785, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3784 c row = (mc 890 + mc 1679 - mc 1294*mc 1679 - 2*mc 890*mc 1679 + 2*mc 890*mc 1294*mc 1679) + 2 * KeccakfPermAir.extraction.inter_3782 c row := by
    simp only [KeccakfPermAir.extraction.inter_3784, KeccakfPermAir.extraction.inter_3783, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3782 c row = (mc 891 + mc 1680 - mc 1295*mc 1680 - 2*mc 891*mc 1680 + 2*mc 891*mc 1295*mc 1680) + 2 * KeccakfPermAir.extraction.inter_3780 c row := by
    simp only [KeccakfPermAir.extraction.inter_3782, KeccakfPermAir.extraction.inter_3781, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3780 c row = (mc 892 + mc 1681 - mc 1296*mc 1681 - 2*mc 892*mc 1681 + 2*mc 892*mc 1296*mc 1681) + 2 * KeccakfPermAir.extraction.inter_3778 c row := by
    simp only [KeccakfPermAir.extraction.inter_3780, KeccakfPermAir.extraction.inter_3779, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3778 c row = (mc 893 + mc 1682 - mc 1297*mc 1682 - 2*mc 893*mc 1682 + 2*mc 893*mc 1297*mc 1682) + 2 * KeccakfPermAir.extraction.inter_3776 c row := by
    simp only [KeccakfPermAir.extraction.inter_3778, KeccakfPermAir.extraction.inter_3777, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3776 c row = (mc 894 + mc 1683 - mc 1298*mc 1683 - 2*mc 894*mc 1683 + 2*mc 894*mc 1298*mc 1683) + 2 * KeccakfPermAir.extraction.inter_3774 c row := by
    simp only [KeccakfPermAir.extraction.inter_3776, KeccakfPermAir.extraction.inter_3775, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3774 c row = (mc 895 + mc 1684 - mc 1299*mc 1684 - 2*mc 895*mc 1684 + 2*mc 895*mc 1299*mc 1684) + 2 * KeccakfPermAir.extraction.inter_3772 c row := by
    simp only [KeccakfPermAir.extraction.inter_3774, KeccakfPermAir.extraction.inter_3773, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3772 c row = (mc 896 + mc 1685 - mc 1300*mc 1685 - 2*mc 896*mc 1685 + 2*mc 896*mc 1300*mc 1685) := by
    simp only [KeccakfPermAir.extraction.inter_3772, KeccakfPermAir.extraction.inter_3771, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2912 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2912 c row) :
    ((mc 897 + mc 1686 - mc 1301*mc 1686 - 2*mc 897*mc 1686 + 2*mc 897*mc 1301*mc 1686) + 2*(mc 898 + mc 1687 - mc 1302*mc 1687 - 2*mc 898*mc 1687 + 2*mc 898*mc 1302*mc 1687) + 4*(mc 899 + mc 1688 - mc 1303*mc 1688 - 2*mc 899*mc 1688 + 2*mc 899*mc 1303*mc 1688) + 8*(mc 900 + mc 1689 - mc 1304*mc 1689 - 2*mc 900*mc 1689 + 2*mc 900*mc 1304*mc 1689) + 16*(mc 901 + mc 1690 - mc 1305*mc 1690 - 2*mc 901*mc 1690 + 2*mc 901*mc 1305*mc 1690) + 32*(mc 902 + mc 1691 - mc 1306*mc 1691 - 2*mc 902*mc 1691 + 2*mc 902*mc 1306*mc 1691) + 64*(mc 903 + mc 1692 - mc 1307*mc 1692 - 2*mc 903*mc 1692 + 2*mc 903*mc 1307*mc 1692) + 128*(mc 904 + mc 1693 - mc 1308*mc 1693 - 2*mc 904*mc 1693 + 2*mc 904*mc 1308*mc 1693) + 256*(mc 905 + mc 1694 - mc 1309*mc 1694 - 2*mc 905*mc 1694 + 2*mc 905*mc 1309*mc 1694) + 512*(mc 906 + mc 1695 - mc 1310*mc 1695 - 2*mc 906*mc 1695 + 2*mc 906*mc 1310*mc 1695) + 1024*(mc 907 + mc 1696 - mc 1311*mc 1696 - 2*mc 907*mc 1696 + 2*mc 907*mc 1311*mc 1696) + 2048*(mc 908 + mc 1633 - mc 1312*mc 1633 - 2*mc 908*mc 1633 + 2*mc 908*mc 1312*mc 1633) + 4096*(mc 909 + mc 1634 - mc 1249*mc 1634 - 2*mc 909*mc 1634 + 2*mc 909*mc 1249*mc 1634) + 8192*(mc 910 + mc 1635 - mc 1250*mc 1635 - 2*mc 910*mc 1635 + 2*mc 910*mc 1250*mc 1635) + 16384*(mc 911 + mc 1636 - mc 1251*mc 1636 - 2*mc 911*mc 1636 + 2*mc 911*mc 1251*mc 1636) + 32768*(mc 912 + mc 1637 - mc 1252*mc 1637 - 2*mc 912*mc 1637 + 2*mc 912*mc 1252*mc 1637)) - mc 2467 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2912, KeccakfPermAir.extraction.inter_3832, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3831 c row = (mc 898 + mc 1687 - mc 1302*mc 1687 - 2*mc 898*mc 1687 + 2*mc 898*mc 1302*mc 1687) + 2 * KeccakfPermAir.extraction.inter_3829 c row := by
    simp only [KeccakfPermAir.extraction.inter_3831, KeccakfPermAir.extraction.inter_3830, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3829 c row = (mc 899 + mc 1688 - mc 1303*mc 1688 - 2*mc 899*mc 1688 + 2*mc 899*mc 1303*mc 1688) + 2 * KeccakfPermAir.extraction.inter_3827 c row := by
    simp only [KeccakfPermAir.extraction.inter_3829, KeccakfPermAir.extraction.inter_3828, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3827 c row = (mc 900 + mc 1689 - mc 1304*mc 1689 - 2*mc 900*mc 1689 + 2*mc 900*mc 1304*mc 1689) + 2 * KeccakfPermAir.extraction.inter_3825 c row := by
    simp only [KeccakfPermAir.extraction.inter_3827, KeccakfPermAir.extraction.inter_3826, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3825 c row = (mc 901 + mc 1690 - mc 1305*mc 1690 - 2*mc 901*mc 1690 + 2*mc 901*mc 1305*mc 1690) + 2 * KeccakfPermAir.extraction.inter_3823 c row := by
    simp only [KeccakfPermAir.extraction.inter_3825, KeccakfPermAir.extraction.inter_3824, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3823 c row = (mc 902 + mc 1691 - mc 1306*mc 1691 - 2*mc 902*mc 1691 + 2*mc 902*mc 1306*mc 1691) + 2 * KeccakfPermAir.extraction.inter_3821 c row := by
    simp only [KeccakfPermAir.extraction.inter_3823, KeccakfPermAir.extraction.inter_3822, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3821 c row = (mc 903 + mc 1692 - mc 1307*mc 1692 - 2*mc 903*mc 1692 + 2*mc 903*mc 1307*mc 1692) + 2 * KeccakfPermAir.extraction.inter_3819 c row := by
    simp only [KeccakfPermAir.extraction.inter_3821, KeccakfPermAir.extraction.inter_3820, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3819 c row = (mc 904 + mc 1693 - mc 1308*mc 1693 - 2*mc 904*mc 1693 + 2*mc 904*mc 1308*mc 1693) + 2 * KeccakfPermAir.extraction.inter_3817 c row := by
    simp only [KeccakfPermAir.extraction.inter_3819, KeccakfPermAir.extraction.inter_3818, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3817 c row = (mc 905 + mc 1694 - mc 1309*mc 1694 - 2*mc 905*mc 1694 + 2*mc 905*mc 1309*mc 1694) + 2 * KeccakfPermAir.extraction.inter_3815 c row := by
    simp only [KeccakfPermAir.extraction.inter_3817, KeccakfPermAir.extraction.inter_3816, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3815 c row = (mc 906 + mc 1695 - mc 1310*mc 1695 - 2*mc 906*mc 1695 + 2*mc 906*mc 1310*mc 1695) + 2 * KeccakfPermAir.extraction.inter_3813 c row := by
    simp only [KeccakfPermAir.extraction.inter_3815, KeccakfPermAir.extraction.inter_3814, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3813 c row = (mc 907 + mc 1696 - mc 1311*mc 1696 - 2*mc 907*mc 1696 + 2*mc 907*mc 1311*mc 1696) + 2 * KeccakfPermAir.extraction.inter_3811 c row := by
    simp only [KeccakfPermAir.extraction.inter_3813, KeccakfPermAir.extraction.inter_3812, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3811 c row = (mc 908 + mc 1633 - mc 1312*mc 1633 - 2*mc 908*mc 1633 + 2*mc 908*mc 1312*mc 1633) + 2 * KeccakfPermAir.extraction.inter_3809 c row := by
    simp only [KeccakfPermAir.extraction.inter_3811, KeccakfPermAir.extraction.inter_3810, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3809 c row = (mc 909 + mc 1634 - mc 1249*mc 1634 - 2*mc 909*mc 1634 + 2*mc 909*mc 1249*mc 1634) + 2 * KeccakfPermAir.extraction.inter_3807 c row := by
    simp only [KeccakfPermAir.extraction.inter_3809, KeccakfPermAir.extraction.inter_3808, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3807 c row = (mc 910 + mc 1635 - mc 1250*mc 1635 - 2*mc 910*mc 1635 + 2*mc 910*mc 1250*mc 1635) + 2 * KeccakfPermAir.extraction.inter_3805 c row := by
    simp only [KeccakfPermAir.extraction.inter_3807, KeccakfPermAir.extraction.inter_3806, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3805 c row = (mc 911 + mc 1636 - mc 1251*mc 1636 - 2*mc 911*mc 1636 + 2*mc 911*mc 1251*mc 1636) + 2 * KeccakfPermAir.extraction.inter_3803 c row := by
    simp only [KeccakfPermAir.extraction.inter_3805, KeccakfPermAir.extraction.inter_3804, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3803 c row = (mc 912 + mc 1637 - mc 1252*mc 1637 - 2*mc 912*mc 1637 + 2*mc 912*mc 1252*mc 1637) := by
    simp only [KeccakfPermAir.extraction.inter_3803, KeccakfPermAir.extraction.inter_3802, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2913 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2913 c row) :
    ((mc 913 + mc 1638 - mc 1253*mc 1638 - 2*mc 913*mc 1638 + 2*mc 913*mc 1253*mc 1638) + 2*(mc 914 + mc 1639 - mc 1254*mc 1639 - 2*mc 914*mc 1639 + 2*mc 914*mc 1254*mc 1639) + 4*(mc 915 + mc 1640 - mc 1255*mc 1640 - 2*mc 915*mc 1640 + 2*mc 915*mc 1255*mc 1640) + 8*(mc 916 + mc 1641 - mc 1256*mc 1641 - 2*mc 916*mc 1641 + 2*mc 916*mc 1256*mc 1641) + 16*(mc 917 + mc 1642 - mc 1257*mc 1642 - 2*mc 917*mc 1642 + 2*mc 917*mc 1257*mc 1642) + 32*(mc 918 + mc 1643 - mc 1258*mc 1643 - 2*mc 918*mc 1643 + 2*mc 918*mc 1258*mc 1643) + 64*(mc 919 + mc 1644 - mc 1259*mc 1644 - 2*mc 919*mc 1644 + 2*mc 919*mc 1259*mc 1644) + 128*(mc 920 + mc 1645 - mc 1260*mc 1645 - 2*mc 920*mc 1645 + 2*mc 920*mc 1260*mc 1645) + 256*(mc 921 + mc 1646 - mc 1261*mc 1646 - 2*mc 921*mc 1646 + 2*mc 921*mc 1261*mc 1646) + 512*(mc 922 + mc 1647 - mc 1262*mc 1647 - 2*mc 922*mc 1647 + 2*mc 922*mc 1262*mc 1647) + 1024*(mc 923 + mc 1648 - mc 1263*mc 1648 - 2*mc 923*mc 1648 + 2*mc 923*mc 1263*mc 1648) + 2048*(mc 924 + mc 1649 - mc 1264*mc 1649 - 2*mc 924*mc 1649 + 2*mc 924*mc 1264*mc 1649) + 4096*(mc 925 + mc 1650 - mc 1265*mc 1650 - 2*mc 925*mc 1650 + 2*mc 925*mc 1265*mc 1650) + 8192*(mc 926 + mc 1651 - mc 1266*mc 1651 - 2*mc 926*mc 1651 + 2*mc 926*mc 1266*mc 1651) + 16384*(mc 927 + mc 1652 - mc 1267*mc 1652 - 2*mc 927*mc 1652 + 2*mc 927*mc 1267*mc 1652) + 32768*(mc 928 + mc 1653 - mc 1268*mc 1653 - 2*mc 928*mc 1653 + 2*mc 928*mc 1268*mc 1653)) - mc 2468 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2913, KeccakfPermAir.extraction.inter_3863, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3862 c row = (mc 914 + mc 1639 - mc 1254*mc 1639 - 2*mc 914*mc 1639 + 2*mc 914*mc 1254*mc 1639) + 2 * KeccakfPermAir.extraction.inter_3860 c row := by
    simp only [KeccakfPermAir.extraction.inter_3862, KeccakfPermAir.extraction.inter_3861, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3860 c row = (mc 915 + mc 1640 - mc 1255*mc 1640 - 2*mc 915*mc 1640 + 2*mc 915*mc 1255*mc 1640) + 2 * KeccakfPermAir.extraction.inter_3858 c row := by
    simp only [KeccakfPermAir.extraction.inter_3860, KeccakfPermAir.extraction.inter_3859, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3858 c row = (mc 916 + mc 1641 - mc 1256*mc 1641 - 2*mc 916*mc 1641 + 2*mc 916*mc 1256*mc 1641) + 2 * KeccakfPermAir.extraction.inter_3856 c row := by
    simp only [KeccakfPermAir.extraction.inter_3858, KeccakfPermAir.extraction.inter_3857, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3856 c row = (mc 917 + mc 1642 - mc 1257*mc 1642 - 2*mc 917*mc 1642 + 2*mc 917*mc 1257*mc 1642) + 2 * KeccakfPermAir.extraction.inter_3854 c row := by
    simp only [KeccakfPermAir.extraction.inter_3856, KeccakfPermAir.extraction.inter_3855, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3854 c row = (mc 918 + mc 1643 - mc 1258*mc 1643 - 2*mc 918*mc 1643 + 2*mc 918*mc 1258*mc 1643) + 2 * KeccakfPermAir.extraction.inter_3852 c row := by
    simp only [KeccakfPermAir.extraction.inter_3854, KeccakfPermAir.extraction.inter_3853, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3852 c row = (mc 919 + mc 1644 - mc 1259*mc 1644 - 2*mc 919*mc 1644 + 2*mc 919*mc 1259*mc 1644) + 2 * KeccakfPermAir.extraction.inter_3850 c row := by
    simp only [KeccakfPermAir.extraction.inter_3852, KeccakfPermAir.extraction.inter_3851, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3850 c row = (mc 920 + mc 1645 - mc 1260*mc 1645 - 2*mc 920*mc 1645 + 2*mc 920*mc 1260*mc 1645) + 2 * KeccakfPermAir.extraction.inter_3848 c row := by
    simp only [KeccakfPermAir.extraction.inter_3850, KeccakfPermAir.extraction.inter_3849, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3848 c row = (mc 921 + mc 1646 - mc 1261*mc 1646 - 2*mc 921*mc 1646 + 2*mc 921*mc 1261*mc 1646) + 2 * KeccakfPermAir.extraction.inter_3846 c row := by
    simp only [KeccakfPermAir.extraction.inter_3848, KeccakfPermAir.extraction.inter_3847, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3846 c row = (mc 922 + mc 1647 - mc 1262*mc 1647 - 2*mc 922*mc 1647 + 2*mc 922*mc 1262*mc 1647) + 2 * KeccakfPermAir.extraction.inter_3844 c row := by
    simp only [KeccakfPermAir.extraction.inter_3846, KeccakfPermAir.extraction.inter_3845, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3844 c row = (mc 923 + mc 1648 - mc 1263*mc 1648 - 2*mc 923*mc 1648 + 2*mc 923*mc 1263*mc 1648) + 2 * KeccakfPermAir.extraction.inter_3842 c row := by
    simp only [KeccakfPermAir.extraction.inter_3844, KeccakfPermAir.extraction.inter_3843, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3842 c row = (mc 924 + mc 1649 - mc 1264*mc 1649 - 2*mc 924*mc 1649 + 2*mc 924*mc 1264*mc 1649) + 2 * KeccakfPermAir.extraction.inter_3840 c row := by
    simp only [KeccakfPermAir.extraction.inter_3842, KeccakfPermAir.extraction.inter_3841, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3840 c row = (mc 925 + mc 1650 - mc 1265*mc 1650 - 2*mc 925*mc 1650 + 2*mc 925*mc 1265*mc 1650) + 2 * KeccakfPermAir.extraction.inter_3838 c row := by
    simp only [KeccakfPermAir.extraction.inter_3840, KeccakfPermAir.extraction.inter_3839, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3838 c row = (mc 926 + mc 1651 - mc 1266*mc 1651 - 2*mc 926*mc 1651 + 2*mc 926*mc 1266*mc 1651) + 2 * KeccakfPermAir.extraction.inter_3836 c row := by
    simp only [KeccakfPermAir.extraction.inter_3838, KeccakfPermAir.extraction.inter_3837, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3836 c row = (mc 927 + mc 1652 - mc 1267*mc 1652 - 2*mc 927*mc 1652 + 2*mc 927*mc 1267*mc 1652) + 2 * KeccakfPermAir.extraction.inter_3834 c row := by
    simp only [KeccakfPermAir.extraction.inter_3836, KeccakfPermAir.extraction.inter_3835, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3834 c row = (mc 928 + mc 1653 - mc 1268*mc 1653 - 2*mc 928*mc 1653 + 2*mc 928*mc 1268*mc 1653) := by
    simp only [KeccakfPermAir.extraction.inter_3834, KeccakfPermAir.extraction.inter_3833, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2914 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2914 c row) :
    ((mc 1269 + mc 2060 - mc 1654*mc 2060 - 2*mc 1269*mc 2060 + 2*mc 1269*mc 1654*mc 2060) + 2*(mc 1270 + mc 2061 - mc 1655*mc 2061 - 2*mc 1270*mc 2061 + 2*mc 1270*mc 1655*mc 2061) + 4*(mc 1271 + mc 2062 - mc 1656*mc 2062 - 2*mc 1271*mc 2062 + 2*mc 1271*mc 1656*mc 2062) + 8*(mc 1272 + mc 2063 - mc 1657*mc 2063 - 2*mc 1272*mc 2063 + 2*mc 1272*mc 1657*mc 2063) + 16*(mc 1273 + mc 2064 - mc 1658*mc 2064 - 2*mc 1273*mc 2064 + 2*mc 1273*mc 1658*mc 2064) + 32*(mc 1274 + mc 2065 - mc 1659*mc 2065 - 2*mc 1274*mc 2065 + 2*mc 1274*mc 1659*mc 2065) + 64*(mc 1275 + mc 2066 - mc 1660*mc 2066 - 2*mc 1275*mc 2066 + 2*mc 1275*mc 1660*mc 2066) + 128*(mc 1276 + mc 2067 - mc 1661*mc 2067 - 2*mc 1276*mc 2067 + 2*mc 1276*mc 1661*mc 2067) + 256*(mc 1277 + mc 2068 - mc 1662*mc 2068 - 2*mc 1277*mc 2068 + 2*mc 1277*mc 1662*mc 2068) + 512*(mc 1278 + mc 2069 - mc 1663*mc 2069 - 2*mc 1278*mc 2069 + 2*mc 1278*mc 1663*mc 2069) + 1024*(mc 1279 + mc 2070 - mc 1664*mc 2070 - 2*mc 1279*mc 2070 + 2*mc 1279*mc 1664*mc 2070) + 2048*(mc 1280 + mc 2071 - mc 1665*mc 2071 - 2*mc 1280*mc 2071 + 2*mc 1280*mc 1665*mc 2071) + 4096*(mc 1281 + mc 2072 - mc 1666*mc 2072 - 2*mc 1281*mc 2072 + 2*mc 1281*mc 1666*mc 2072) + 8192*(mc 1282 + mc 2073 - mc 1667*mc 2073 - 2*mc 1282*mc 2073 + 2*mc 1282*mc 1667*mc 2073) + 16384*(mc 1283 + mc 2074 - mc 1668*mc 2074 - 2*mc 1283*mc 2074 + 2*mc 1283*mc 1668*mc 2074) + 32768*(mc 1284 + mc 2075 - mc 1669*mc 2075 - 2*mc 1284*mc 2075 + 2*mc 1284*mc 1669*mc 2075)) - mc 2469 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2914, KeccakfPermAir.extraction.inter_3894, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3893 c row = (mc 1270 + mc 2061 - mc 1655*mc 2061 - 2*mc 1270*mc 2061 + 2*mc 1270*mc 1655*mc 2061) + 2 * KeccakfPermAir.extraction.inter_3891 c row := by
    simp only [KeccakfPermAir.extraction.inter_3893, KeccakfPermAir.extraction.inter_3892, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3891 c row = (mc 1271 + mc 2062 - mc 1656*mc 2062 - 2*mc 1271*mc 2062 + 2*mc 1271*mc 1656*mc 2062) + 2 * KeccakfPermAir.extraction.inter_3889 c row := by
    simp only [KeccakfPermAir.extraction.inter_3891, KeccakfPermAir.extraction.inter_3890, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3889 c row = (mc 1272 + mc 2063 - mc 1657*mc 2063 - 2*mc 1272*mc 2063 + 2*mc 1272*mc 1657*mc 2063) + 2 * KeccakfPermAir.extraction.inter_3887 c row := by
    simp only [KeccakfPermAir.extraction.inter_3889, KeccakfPermAir.extraction.inter_3888, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3887 c row = (mc 1273 + mc 2064 - mc 1658*mc 2064 - 2*mc 1273*mc 2064 + 2*mc 1273*mc 1658*mc 2064) + 2 * KeccakfPermAir.extraction.inter_3885 c row := by
    simp only [KeccakfPermAir.extraction.inter_3887, KeccakfPermAir.extraction.inter_3886, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3885 c row = (mc 1274 + mc 2065 - mc 1659*mc 2065 - 2*mc 1274*mc 2065 + 2*mc 1274*mc 1659*mc 2065) + 2 * KeccakfPermAir.extraction.inter_3883 c row := by
    simp only [KeccakfPermAir.extraction.inter_3885, KeccakfPermAir.extraction.inter_3884, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3883 c row = (mc 1275 + mc 2066 - mc 1660*mc 2066 - 2*mc 1275*mc 2066 + 2*mc 1275*mc 1660*mc 2066) + 2 * KeccakfPermAir.extraction.inter_3881 c row := by
    simp only [KeccakfPermAir.extraction.inter_3883, KeccakfPermAir.extraction.inter_3882, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3881 c row = (mc 1276 + mc 2067 - mc 1661*mc 2067 - 2*mc 1276*mc 2067 + 2*mc 1276*mc 1661*mc 2067) + 2 * KeccakfPermAir.extraction.inter_3879 c row := by
    simp only [KeccakfPermAir.extraction.inter_3881, KeccakfPermAir.extraction.inter_3880, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3879 c row = (mc 1277 + mc 2068 - mc 1662*mc 2068 - 2*mc 1277*mc 2068 + 2*mc 1277*mc 1662*mc 2068) + 2 * KeccakfPermAir.extraction.inter_3877 c row := by
    simp only [KeccakfPermAir.extraction.inter_3879, KeccakfPermAir.extraction.inter_3878, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3877 c row = (mc 1278 + mc 2069 - mc 1663*mc 2069 - 2*mc 1278*mc 2069 + 2*mc 1278*mc 1663*mc 2069) + 2 * KeccakfPermAir.extraction.inter_3875 c row := by
    simp only [KeccakfPermAir.extraction.inter_3877, KeccakfPermAir.extraction.inter_3876, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3875 c row = (mc 1279 + mc 2070 - mc 1664*mc 2070 - 2*mc 1279*mc 2070 + 2*mc 1279*mc 1664*mc 2070) + 2 * KeccakfPermAir.extraction.inter_3873 c row := by
    simp only [KeccakfPermAir.extraction.inter_3875, KeccakfPermAir.extraction.inter_3874, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3873 c row = (mc 1280 + mc 2071 - mc 1665*mc 2071 - 2*mc 1280*mc 2071 + 2*mc 1280*mc 1665*mc 2071) + 2 * KeccakfPermAir.extraction.inter_3871 c row := by
    simp only [KeccakfPermAir.extraction.inter_3873, KeccakfPermAir.extraction.inter_3872, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3871 c row = (mc 1281 + mc 2072 - mc 1666*mc 2072 - 2*mc 1281*mc 2072 + 2*mc 1281*mc 1666*mc 2072) + 2 * KeccakfPermAir.extraction.inter_3869 c row := by
    simp only [KeccakfPermAir.extraction.inter_3871, KeccakfPermAir.extraction.inter_3870, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3869 c row = (mc 1282 + mc 2073 - mc 1667*mc 2073 - 2*mc 1282*mc 2073 + 2*mc 1282*mc 1667*mc 2073) + 2 * KeccakfPermAir.extraction.inter_3867 c row := by
    simp only [KeccakfPermAir.extraction.inter_3869, KeccakfPermAir.extraction.inter_3868, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3867 c row = (mc 1283 + mc 2074 - mc 1668*mc 2074 - 2*mc 1283*mc 2074 + 2*mc 1283*mc 1668*mc 2074) + 2 * KeccakfPermAir.extraction.inter_3865 c row := by
    simp only [KeccakfPermAir.extraction.inter_3867, KeccakfPermAir.extraction.inter_3866, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3865 c row = (mc 1284 + mc 2075 - mc 1669*mc 2075 - 2*mc 1284*mc 2075 + 2*mc 1284*mc 1669*mc 2075) := by
    simp only [KeccakfPermAir.extraction.inter_3865, KeccakfPermAir.extraction.inter_3864, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2915 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2915 c row) :
    ((mc 1285 + mc 2076 - mc 1670*mc 2076 - 2*mc 1285*mc 2076 + 2*mc 1285*mc 1670*mc 2076) + 2*(mc 1286 + mc 2077 - mc 1671*mc 2077 - 2*mc 1286*mc 2077 + 2*mc 1286*mc 1671*mc 2077) + 4*(mc 1287 + mc 2078 - mc 1672*mc 2078 - 2*mc 1287*mc 2078 + 2*mc 1287*mc 1672*mc 2078) + 8*(mc 1288 + mc 2079 - mc 1673*mc 2079 - 2*mc 1288*mc 2079 + 2*mc 1288*mc 1673*mc 2079) + 16*(mc 1289 + mc 2080 - mc 1674*mc 2080 - 2*mc 1289*mc 2080 + 2*mc 1289*mc 1674*mc 2080) + 32*(mc 1290 + mc 2017 - mc 1675*mc 2017 - 2*mc 1290*mc 2017 + 2*mc 1290*mc 1675*mc 2017) + 64*(mc 1291 + mc 2018 - mc 1676*mc 2018 - 2*mc 1291*mc 2018 + 2*mc 1291*mc 1676*mc 2018) + 128*(mc 1292 + mc 2019 - mc 1677*mc 2019 - 2*mc 1292*mc 2019 + 2*mc 1292*mc 1677*mc 2019) + 256*(mc 1293 + mc 2020 - mc 1678*mc 2020 - 2*mc 1293*mc 2020 + 2*mc 1293*mc 1678*mc 2020) + 512*(mc 1294 + mc 2021 - mc 1679*mc 2021 - 2*mc 1294*mc 2021 + 2*mc 1294*mc 1679*mc 2021) + 1024*(mc 1295 + mc 2022 - mc 1680*mc 2022 - 2*mc 1295*mc 2022 + 2*mc 1295*mc 1680*mc 2022) + 2048*(mc 1296 + mc 2023 - mc 1681*mc 2023 - 2*mc 1296*mc 2023 + 2*mc 1296*mc 1681*mc 2023) + 4096*(mc 1297 + mc 2024 - mc 1682*mc 2024 - 2*mc 1297*mc 2024 + 2*mc 1297*mc 1682*mc 2024) + 8192*(mc 1298 + mc 2025 - mc 1683*mc 2025 - 2*mc 1298*mc 2025 + 2*mc 1298*mc 1683*mc 2025) + 16384*(mc 1299 + mc 2026 - mc 1684*mc 2026 - 2*mc 1299*mc 2026 + 2*mc 1299*mc 1684*mc 2026) + 32768*(mc 1300 + mc 2027 - mc 1685*mc 2027 - 2*mc 1300*mc 2027 + 2*mc 1300*mc 1685*mc 2027)) - mc 2470 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2915, KeccakfPermAir.extraction.inter_3925, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3924 c row = (mc 1286 + mc 2077 - mc 1671*mc 2077 - 2*mc 1286*mc 2077 + 2*mc 1286*mc 1671*mc 2077) + 2 * KeccakfPermAir.extraction.inter_3922 c row := by
    simp only [KeccakfPermAir.extraction.inter_3924, KeccakfPermAir.extraction.inter_3923, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3922 c row = (mc 1287 + mc 2078 - mc 1672*mc 2078 - 2*mc 1287*mc 2078 + 2*mc 1287*mc 1672*mc 2078) + 2 * KeccakfPermAir.extraction.inter_3920 c row := by
    simp only [KeccakfPermAir.extraction.inter_3922, KeccakfPermAir.extraction.inter_3921, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3920 c row = (mc 1288 + mc 2079 - mc 1673*mc 2079 - 2*mc 1288*mc 2079 + 2*mc 1288*mc 1673*mc 2079) + 2 * KeccakfPermAir.extraction.inter_3918 c row := by
    simp only [KeccakfPermAir.extraction.inter_3920, KeccakfPermAir.extraction.inter_3919, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3918 c row = (mc 1289 + mc 2080 - mc 1674*mc 2080 - 2*mc 1289*mc 2080 + 2*mc 1289*mc 1674*mc 2080) + 2 * KeccakfPermAir.extraction.inter_3916 c row := by
    simp only [KeccakfPermAir.extraction.inter_3918, KeccakfPermAir.extraction.inter_3917, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3916 c row = (mc 1290 + mc 2017 - mc 1675*mc 2017 - 2*mc 1290*mc 2017 + 2*mc 1290*mc 1675*mc 2017) + 2 * KeccakfPermAir.extraction.inter_3914 c row := by
    simp only [KeccakfPermAir.extraction.inter_3916, KeccakfPermAir.extraction.inter_3915, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3914 c row = (mc 1291 + mc 2018 - mc 1676*mc 2018 - 2*mc 1291*mc 2018 + 2*mc 1291*mc 1676*mc 2018) + 2 * KeccakfPermAir.extraction.inter_3912 c row := by
    simp only [KeccakfPermAir.extraction.inter_3914, KeccakfPermAir.extraction.inter_3913, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3912 c row = (mc 1292 + mc 2019 - mc 1677*mc 2019 - 2*mc 1292*mc 2019 + 2*mc 1292*mc 1677*mc 2019) + 2 * KeccakfPermAir.extraction.inter_3910 c row := by
    simp only [KeccakfPermAir.extraction.inter_3912, KeccakfPermAir.extraction.inter_3911, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3910 c row = (mc 1293 + mc 2020 - mc 1678*mc 2020 - 2*mc 1293*mc 2020 + 2*mc 1293*mc 1678*mc 2020) + 2 * KeccakfPermAir.extraction.inter_3908 c row := by
    simp only [KeccakfPermAir.extraction.inter_3910, KeccakfPermAir.extraction.inter_3909, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3908 c row = (mc 1294 + mc 2021 - mc 1679*mc 2021 - 2*mc 1294*mc 2021 + 2*mc 1294*mc 1679*mc 2021) + 2 * KeccakfPermAir.extraction.inter_3906 c row := by
    simp only [KeccakfPermAir.extraction.inter_3908, KeccakfPermAir.extraction.inter_3907, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3906 c row = (mc 1295 + mc 2022 - mc 1680*mc 2022 - 2*mc 1295*mc 2022 + 2*mc 1295*mc 1680*mc 2022) + 2 * KeccakfPermAir.extraction.inter_3904 c row := by
    simp only [KeccakfPermAir.extraction.inter_3906, KeccakfPermAir.extraction.inter_3905, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3904 c row = (mc 1296 + mc 2023 - mc 1681*mc 2023 - 2*mc 1296*mc 2023 + 2*mc 1296*mc 1681*mc 2023) + 2 * KeccakfPermAir.extraction.inter_3902 c row := by
    simp only [KeccakfPermAir.extraction.inter_3904, KeccakfPermAir.extraction.inter_3903, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3902 c row = (mc 1297 + mc 2024 - mc 1682*mc 2024 - 2*mc 1297*mc 2024 + 2*mc 1297*mc 1682*mc 2024) + 2 * KeccakfPermAir.extraction.inter_3900 c row := by
    simp only [KeccakfPermAir.extraction.inter_3902, KeccakfPermAir.extraction.inter_3901, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3900 c row = (mc 1298 + mc 2025 - mc 1683*mc 2025 - 2*mc 1298*mc 2025 + 2*mc 1298*mc 1683*mc 2025) + 2 * KeccakfPermAir.extraction.inter_3898 c row := by
    simp only [KeccakfPermAir.extraction.inter_3900, KeccakfPermAir.extraction.inter_3899, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3898 c row = (mc 1299 + mc 2026 - mc 1684*mc 2026 - 2*mc 1299*mc 2026 + 2*mc 1299*mc 1684*mc 2026) + 2 * KeccakfPermAir.extraction.inter_3896 c row := by
    simp only [KeccakfPermAir.extraction.inter_3898, KeccakfPermAir.extraction.inter_3897, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3896 c row = (mc 1300 + mc 2027 - mc 1685*mc 2027 - 2*mc 1300*mc 2027 + 2*mc 1300*mc 1685*mc 2027) := by
    simp only [KeccakfPermAir.extraction.inter_3896, KeccakfPermAir.extraction.inter_3895, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2916 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2916 c row) :
    ((mc 1301 + mc 2028 - mc 1686*mc 2028 - 2*mc 1301*mc 2028 + 2*mc 1301*mc 1686*mc 2028) + 2*(mc 1302 + mc 2029 - mc 1687*mc 2029 - 2*mc 1302*mc 2029 + 2*mc 1302*mc 1687*mc 2029) + 4*(mc 1303 + mc 2030 - mc 1688*mc 2030 - 2*mc 1303*mc 2030 + 2*mc 1303*mc 1688*mc 2030) + 8*(mc 1304 + mc 2031 - mc 1689*mc 2031 - 2*mc 1304*mc 2031 + 2*mc 1304*mc 1689*mc 2031) + 16*(mc 1305 + mc 2032 - mc 1690*mc 2032 - 2*mc 1305*mc 2032 + 2*mc 1305*mc 1690*mc 2032) + 32*(mc 1306 + mc 2033 - mc 1691*mc 2033 - 2*mc 1306*mc 2033 + 2*mc 1306*mc 1691*mc 2033) + 64*(mc 1307 + mc 2034 - mc 1692*mc 2034 - 2*mc 1307*mc 2034 + 2*mc 1307*mc 1692*mc 2034) + 128*(mc 1308 + mc 2035 - mc 1693*mc 2035 - 2*mc 1308*mc 2035 + 2*mc 1308*mc 1693*mc 2035) + 256*(mc 1309 + mc 2036 - mc 1694*mc 2036 - 2*mc 1309*mc 2036 + 2*mc 1309*mc 1694*mc 2036) + 512*(mc 1310 + mc 2037 - mc 1695*mc 2037 - 2*mc 1310*mc 2037 + 2*mc 1310*mc 1695*mc 2037) + 1024*(mc 1311 + mc 2038 - mc 1696*mc 2038 - 2*mc 1311*mc 2038 + 2*mc 1311*mc 1696*mc 2038) + 2048*(mc 1312 + mc 2039 - mc 1633*mc 2039 - 2*mc 1312*mc 2039 + 2*mc 1312*mc 1633*mc 2039) + 4096*(mc 1249 + mc 2040 - mc 1634*mc 2040 - 2*mc 1249*mc 2040 + 2*mc 1249*mc 1634*mc 2040) + 8192*(mc 1250 + mc 2041 - mc 1635*mc 2041 - 2*mc 1250*mc 2041 + 2*mc 1250*mc 1635*mc 2041) + 16384*(mc 1251 + mc 2042 - mc 1636*mc 2042 - 2*mc 1251*mc 2042 + 2*mc 1251*mc 1636*mc 2042) + 32768*(mc 1252 + mc 2043 - mc 1637*mc 2043 - 2*mc 1252*mc 2043 + 2*mc 1252*mc 1637*mc 2043)) - mc 2471 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2916, KeccakfPermAir.extraction.inter_3956, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3955 c row = (mc 1302 + mc 2029 - mc 1687*mc 2029 - 2*mc 1302*mc 2029 + 2*mc 1302*mc 1687*mc 2029) + 2 * KeccakfPermAir.extraction.inter_3953 c row := by
    simp only [KeccakfPermAir.extraction.inter_3955, KeccakfPermAir.extraction.inter_3954, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3953 c row = (mc 1303 + mc 2030 - mc 1688*mc 2030 - 2*mc 1303*mc 2030 + 2*mc 1303*mc 1688*mc 2030) + 2 * KeccakfPermAir.extraction.inter_3951 c row := by
    simp only [KeccakfPermAir.extraction.inter_3953, KeccakfPermAir.extraction.inter_3952, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3951 c row = (mc 1304 + mc 2031 - mc 1689*mc 2031 - 2*mc 1304*mc 2031 + 2*mc 1304*mc 1689*mc 2031) + 2 * KeccakfPermAir.extraction.inter_3949 c row := by
    simp only [KeccakfPermAir.extraction.inter_3951, KeccakfPermAir.extraction.inter_3950, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3949 c row = (mc 1305 + mc 2032 - mc 1690*mc 2032 - 2*mc 1305*mc 2032 + 2*mc 1305*mc 1690*mc 2032) + 2 * KeccakfPermAir.extraction.inter_3947 c row := by
    simp only [KeccakfPermAir.extraction.inter_3949, KeccakfPermAir.extraction.inter_3948, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3947 c row = (mc 1306 + mc 2033 - mc 1691*mc 2033 - 2*mc 1306*mc 2033 + 2*mc 1306*mc 1691*mc 2033) + 2 * KeccakfPermAir.extraction.inter_3945 c row := by
    simp only [KeccakfPermAir.extraction.inter_3947, KeccakfPermAir.extraction.inter_3946, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3945 c row = (mc 1307 + mc 2034 - mc 1692*mc 2034 - 2*mc 1307*mc 2034 + 2*mc 1307*mc 1692*mc 2034) + 2 * KeccakfPermAir.extraction.inter_3943 c row := by
    simp only [KeccakfPermAir.extraction.inter_3945, KeccakfPermAir.extraction.inter_3944, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3943 c row = (mc 1308 + mc 2035 - mc 1693*mc 2035 - 2*mc 1308*mc 2035 + 2*mc 1308*mc 1693*mc 2035) + 2 * KeccakfPermAir.extraction.inter_3941 c row := by
    simp only [KeccakfPermAir.extraction.inter_3943, KeccakfPermAir.extraction.inter_3942, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3941 c row = (mc 1309 + mc 2036 - mc 1694*mc 2036 - 2*mc 1309*mc 2036 + 2*mc 1309*mc 1694*mc 2036) + 2 * KeccakfPermAir.extraction.inter_3939 c row := by
    simp only [KeccakfPermAir.extraction.inter_3941, KeccakfPermAir.extraction.inter_3940, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3939 c row = (mc 1310 + mc 2037 - mc 1695*mc 2037 - 2*mc 1310*mc 2037 + 2*mc 1310*mc 1695*mc 2037) + 2 * KeccakfPermAir.extraction.inter_3937 c row := by
    simp only [KeccakfPermAir.extraction.inter_3939, KeccakfPermAir.extraction.inter_3938, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3937 c row = (mc 1311 + mc 2038 - mc 1696*mc 2038 - 2*mc 1311*mc 2038 + 2*mc 1311*mc 1696*mc 2038) + 2 * KeccakfPermAir.extraction.inter_3935 c row := by
    simp only [KeccakfPermAir.extraction.inter_3937, KeccakfPermAir.extraction.inter_3936, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3935 c row = (mc 1312 + mc 2039 - mc 1633*mc 2039 - 2*mc 1312*mc 2039 + 2*mc 1312*mc 1633*mc 2039) + 2 * KeccakfPermAir.extraction.inter_3933 c row := by
    simp only [KeccakfPermAir.extraction.inter_3935, KeccakfPermAir.extraction.inter_3934, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3933 c row = (mc 1249 + mc 2040 - mc 1634*mc 2040 - 2*mc 1249*mc 2040 + 2*mc 1249*mc 1634*mc 2040) + 2 * KeccakfPermAir.extraction.inter_3931 c row := by
    simp only [KeccakfPermAir.extraction.inter_3933, KeccakfPermAir.extraction.inter_3932, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3931 c row = (mc 1250 + mc 2041 - mc 1635*mc 2041 - 2*mc 1250*mc 2041 + 2*mc 1250*mc 1635*mc 2041) + 2 * KeccakfPermAir.extraction.inter_3929 c row := by
    simp only [KeccakfPermAir.extraction.inter_3931, KeccakfPermAir.extraction.inter_3930, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3929 c row = (mc 1251 + mc 2042 - mc 1636*mc 2042 - 2*mc 1251*mc 2042 + 2*mc 1251*mc 1636*mc 2042) + 2 * KeccakfPermAir.extraction.inter_3927 c row := by
    simp only [KeccakfPermAir.extraction.inter_3929, KeccakfPermAir.extraction.inter_3928, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3927 c row = (mc 1252 + mc 2043 - mc 1637*mc 2043 - 2*mc 1252*mc 2043 + 2*mc 1252*mc 1637*mc 2043) := by
    simp only [KeccakfPermAir.extraction.inter_3927, KeccakfPermAir.extraction.inter_3926, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2917 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2917 c row) :
    ((mc 1253 + mc 2044 - mc 1638*mc 2044 - 2*mc 1253*mc 2044 + 2*mc 1253*mc 1638*mc 2044) + 2*(mc 1254 + mc 2045 - mc 1639*mc 2045 - 2*mc 1254*mc 2045 + 2*mc 1254*mc 1639*mc 2045) + 4*(mc 1255 + mc 2046 - mc 1640*mc 2046 - 2*mc 1255*mc 2046 + 2*mc 1255*mc 1640*mc 2046) + 8*(mc 1256 + mc 2047 - mc 1641*mc 2047 - 2*mc 1256*mc 2047 + 2*mc 1256*mc 1641*mc 2047) + 16*(mc 1257 + mc 2048 - mc 1642*mc 2048 - 2*mc 1257*mc 2048 + 2*mc 1257*mc 1642*mc 2048) + 32*(mc 1258 + mc 2049 - mc 1643*mc 2049 - 2*mc 1258*mc 2049 + 2*mc 1258*mc 1643*mc 2049) + 64*(mc 1259 + mc 2050 - mc 1644*mc 2050 - 2*mc 1259*mc 2050 + 2*mc 1259*mc 1644*mc 2050) + 128*(mc 1260 + mc 2051 - mc 1645*mc 2051 - 2*mc 1260*mc 2051 + 2*mc 1260*mc 1645*mc 2051) + 256*(mc 1261 + mc 2052 - mc 1646*mc 2052 - 2*mc 1261*mc 2052 + 2*mc 1261*mc 1646*mc 2052) + 512*(mc 1262 + mc 2053 - mc 1647*mc 2053 - 2*mc 1262*mc 2053 + 2*mc 1262*mc 1647*mc 2053) + 1024*(mc 1263 + mc 2054 - mc 1648*mc 2054 - 2*mc 1263*mc 2054 + 2*mc 1263*mc 1648*mc 2054) + 2048*(mc 1264 + mc 2055 - mc 1649*mc 2055 - 2*mc 1264*mc 2055 + 2*mc 1264*mc 1649*mc 2055) + 4096*(mc 1265 + mc 2056 - mc 1650*mc 2056 - 2*mc 1265*mc 2056 + 2*mc 1265*mc 1650*mc 2056) + 8192*(mc 1266 + mc 2057 - mc 1651*mc 2057 - 2*mc 1266*mc 2057 + 2*mc 1266*mc 1651*mc 2057) + 16384*(mc 1267 + mc 2058 - mc 1652*mc 2058 - 2*mc 1267*mc 2058 + 2*mc 1267*mc 1652*mc 2058) + 32768*(mc 1268 + mc 2059 - mc 1653*mc 2059 - 2*mc 1268*mc 2059 + 2*mc 1268*mc 1653*mc 2059)) - mc 2472 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2917, KeccakfPermAir.extraction.inter_3987, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_3986 c row = (mc 1254 + mc 2045 - mc 1639*mc 2045 - 2*mc 1254*mc 2045 + 2*mc 1254*mc 1639*mc 2045) + 2 * KeccakfPermAir.extraction.inter_3984 c row := by
    simp only [KeccakfPermAir.extraction.inter_3986, KeccakfPermAir.extraction.inter_3985, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_3984 c row = (mc 1255 + mc 2046 - mc 1640*mc 2046 - 2*mc 1255*mc 2046 + 2*mc 1255*mc 1640*mc 2046) + 2 * KeccakfPermAir.extraction.inter_3982 c row := by
    simp only [KeccakfPermAir.extraction.inter_3984, KeccakfPermAir.extraction.inter_3983, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_3982 c row = (mc 1256 + mc 2047 - mc 1641*mc 2047 - 2*mc 1256*mc 2047 + 2*mc 1256*mc 1641*mc 2047) + 2 * KeccakfPermAir.extraction.inter_3980 c row := by
    simp only [KeccakfPermAir.extraction.inter_3982, KeccakfPermAir.extraction.inter_3981, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_3980 c row = (mc 1257 + mc 2048 - mc 1642*mc 2048 - 2*mc 1257*mc 2048 + 2*mc 1257*mc 1642*mc 2048) + 2 * KeccakfPermAir.extraction.inter_3978 c row := by
    simp only [KeccakfPermAir.extraction.inter_3980, KeccakfPermAir.extraction.inter_3979, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_3978 c row = (mc 1258 + mc 2049 - mc 1643*mc 2049 - 2*mc 1258*mc 2049 + 2*mc 1258*mc 1643*mc 2049) + 2 * KeccakfPermAir.extraction.inter_3976 c row := by
    simp only [KeccakfPermAir.extraction.inter_3978, KeccakfPermAir.extraction.inter_3977, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_3976 c row = (mc 1259 + mc 2050 - mc 1644*mc 2050 - 2*mc 1259*mc 2050 + 2*mc 1259*mc 1644*mc 2050) + 2 * KeccakfPermAir.extraction.inter_3974 c row := by
    simp only [KeccakfPermAir.extraction.inter_3976, KeccakfPermAir.extraction.inter_3975, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_3974 c row = (mc 1260 + mc 2051 - mc 1645*mc 2051 - 2*mc 1260*mc 2051 + 2*mc 1260*mc 1645*mc 2051) + 2 * KeccakfPermAir.extraction.inter_3972 c row := by
    simp only [KeccakfPermAir.extraction.inter_3974, KeccakfPermAir.extraction.inter_3973, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_3972 c row = (mc 1261 + mc 2052 - mc 1646*mc 2052 - 2*mc 1261*mc 2052 + 2*mc 1261*mc 1646*mc 2052) + 2 * KeccakfPermAir.extraction.inter_3970 c row := by
    simp only [KeccakfPermAir.extraction.inter_3972, KeccakfPermAir.extraction.inter_3971, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_3970 c row = (mc 1262 + mc 2053 - mc 1647*mc 2053 - 2*mc 1262*mc 2053 + 2*mc 1262*mc 1647*mc 2053) + 2 * KeccakfPermAir.extraction.inter_3968 c row := by
    simp only [KeccakfPermAir.extraction.inter_3970, KeccakfPermAir.extraction.inter_3969, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3968 c row = (mc 1263 + mc 2054 - mc 1648*mc 2054 - 2*mc 1263*mc 2054 + 2*mc 1263*mc 1648*mc 2054) + 2 * KeccakfPermAir.extraction.inter_3966 c row := by
    simp only [KeccakfPermAir.extraction.inter_3968, KeccakfPermAir.extraction.inter_3967, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3966 c row = (mc 1264 + mc 2055 - mc 1649*mc 2055 - 2*mc 1264*mc 2055 + 2*mc 1264*mc 1649*mc 2055) + 2 * KeccakfPermAir.extraction.inter_3964 c row := by
    simp only [KeccakfPermAir.extraction.inter_3966, KeccakfPermAir.extraction.inter_3965, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3964 c row = (mc 1265 + mc 2056 - mc 1650*mc 2056 - 2*mc 1265*mc 2056 + 2*mc 1265*mc 1650*mc 2056) + 2 * KeccakfPermAir.extraction.inter_3962 c row := by
    simp only [KeccakfPermAir.extraction.inter_3964, KeccakfPermAir.extraction.inter_3963, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3962 c row = (mc 1266 + mc 2057 - mc 1651*mc 2057 - 2*mc 1266*mc 2057 + 2*mc 1266*mc 1651*mc 2057) + 2 * KeccakfPermAir.extraction.inter_3960 c row := by
    simp only [KeccakfPermAir.extraction.inter_3962, KeccakfPermAir.extraction.inter_3961, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3960 c row = (mc 1267 + mc 2058 - mc 1652*mc 2058 - 2*mc 1267*mc 2058 + 2*mc 1267*mc 1652*mc 2058) + 2 * KeccakfPermAir.extraction.inter_3958 c row := by
    simp only [KeccakfPermAir.extraction.inter_3960, KeccakfPermAir.extraction.inter_3959, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3958 c row = (mc 1268 + mc 2059 - mc 1653*mc 2059 - 2*mc 1268*mc 2059 + 2*mc 1268*mc 1653*mc 2059) := by
    simp only [KeccakfPermAir.extraction.inter_3958, KeccakfPermAir.extraction.inter_3957, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2918 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2918 c row) :
    ((mc 1654 + mc 2451 - mc 2060*mc 2451 - 2*mc 1654*mc 2451 + 2*mc 1654*mc 2060*mc 2451) + 2*(mc 1655 + mc 2452 - mc 2061*mc 2452 - 2*mc 1655*mc 2452 + 2*mc 1655*mc 2061*mc 2452) + 4*(mc 1656 + mc 2453 - mc 2062*mc 2453 - 2*mc 1656*mc 2453 + 2*mc 1656*mc 2062*mc 2453) + 8*(mc 1657 + mc 2454 - mc 2063*mc 2454 - 2*mc 1657*mc 2454 + 2*mc 1657*mc 2063*mc 2454) + 16*(mc 1658 + mc 2455 - mc 2064*mc 2455 - 2*mc 1658*mc 2455 + 2*mc 1658*mc 2064*mc 2455) + 32*(mc 1659 + mc 2456 - mc 2065*mc 2456 - 2*mc 1659*mc 2456 + 2*mc 1659*mc 2065*mc 2456) + 64*(mc 1660 + mc 2457 - mc 2066*mc 2457 - 2*mc 1660*mc 2457 + 2*mc 1660*mc 2066*mc 2457) + 128*(mc 1661 + mc 2458 - mc 2067*mc 2458 - 2*mc 1661*mc 2458 + 2*mc 1661*mc 2067*mc 2458) + 256*(mc 1662 + mc 2459 - mc 2068*mc 2459 - 2*mc 1662*mc 2459 + 2*mc 1662*mc 2068*mc 2459) + 512*(mc 1663 + mc 2460 - mc 2069*mc 2460 - 2*mc 1663*mc 2460 + 2*mc 1663*mc 2069*mc 2460) + 1024*(mc 1664 + mc 2461 - mc 2070*mc 2461 - 2*mc 1664*mc 2461 + 2*mc 1664*mc 2070*mc 2461) + 2048*(mc 1665 + mc 2462 - mc 2071*mc 2462 - 2*mc 1665*mc 2462 + 2*mc 1665*mc 2071*mc 2462) + 4096*(mc 1666 + mc 2463 - mc 2072*mc 2463 - 2*mc 1666*mc 2463 + 2*mc 1666*mc 2072*mc 2463) + 8192*(mc 1667 + mc 2464 - mc 2073*mc 2464 - 2*mc 1667*mc 2464 + 2*mc 1667*mc 2073*mc 2464) + 16384*(mc 1668 + mc 2401 - mc 2074*mc 2401 - 2*mc 1668*mc 2401 + 2*mc 1668*mc 2074*mc 2401) + 32768*(mc 1669 + mc 2402 - mc 2075*mc 2402 - 2*mc 1669*mc 2402 + 2*mc 1669*mc 2075*mc 2402)) - mc 2473 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2918, KeccakfPermAir.extraction.inter_4018, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4017 c row = (mc 1655 + mc 2452 - mc 2061*mc 2452 - 2*mc 1655*mc 2452 + 2*mc 1655*mc 2061*mc 2452) + 2 * KeccakfPermAir.extraction.inter_4015 c row := by
    simp only [KeccakfPermAir.extraction.inter_4017, KeccakfPermAir.extraction.inter_4016, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4015 c row = (mc 1656 + mc 2453 - mc 2062*mc 2453 - 2*mc 1656*mc 2453 + 2*mc 1656*mc 2062*mc 2453) + 2 * KeccakfPermAir.extraction.inter_4013 c row := by
    simp only [KeccakfPermAir.extraction.inter_4015, KeccakfPermAir.extraction.inter_4014, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4013 c row = (mc 1657 + mc 2454 - mc 2063*mc 2454 - 2*mc 1657*mc 2454 + 2*mc 1657*mc 2063*mc 2454) + 2 * KeccakfPermAir.extraction.inter_4011 c row := by
    simp only [KeccakfPermAir.extraction.inter_4013, KeccakfPermAir.extraction.inter_4012, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4011 c row = (mc 1658 + mc 2455 - mc 2064*mc 2455 - 2*mc 1658*mc 2455 + 2*mc 1658*mc 2064*mc 2455) + 2 * KeccakfPermAir.extraction.inter_4009 c row := by
    simp only [KeccakfPermAir.extraction.inter_4011, KeccakfPermAir.extraction.inter_4010, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4009 c row = (mc 1659 + mc 2456 - mc 2065*mc 2456 - 2*mc 1659*mc 2456 + 2*mc 1659*mc 2065*mc 2456) + 2 * KeccakfPermAir.extraction.inter_4007 c row := by
    simp only [KeccakfPermAir.extraction.inter_4009, KeccakfPermAir.extraction.inter_4008, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4007 c row = (mc 1660 + mc 2457 - mc 2066*mc 2457 - 2*mc 1660*mc 2457 + 2*mc 1660*mc 2066*mc 2457) + 2 * KeccakfPermAir.extraction.inter_4005 c row := by
    simp only [KeccakfPermAir.extraction.inter_4007, KeccakfPermAir.extraction.inter_4006, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4005 c row = (mc 1661 + mc 2458 - mc 2067*mc 2458 - 2*mc 1661*mc 2458 + 2*mc 1661*mc 2067*mc 2458) + 2 * KeccakfPermAir.extraction.inter_4003 c row := by
    simp only [KeccakfPermAir.extraction.inter_4005, KeccakfPermAir.extraction.inter_4004, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4003 c row = (mc 1662 + mc 2459 - mc 2068*mc 2459 - 2*mc 1662*mc 2459 + 2*mc 1662*mc 2068*mc 2459) + 2 * KeccakfPermAir.extraction.inter_4001 c row := by
    simp only [KeccakfPermAir.extraction.inter_4003, KeccakfPermAir.extraction.inter_4002, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4001 c row = (mc 1663 + mc 2460 - mc 2069*mc 2460 - 2*mc 1663*mc 2460 + 2*mc 1663*mc 2069*mc 2460) + 2 * KeccakfPermAir.extraction.inter_3999 c row := by
    simp only [KeccakfPermAir.extraction.inter_4001, KeccakfPermAir.extraction.inter_4000, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_3999 c row = (mc 1664 + mc 2461 - mc 2070*mc 2461 - 2*mc 1664*mc 2461 + 2*mc 1664*mc 2070*mc 2461) + 2 * KeccakfPermAir.extraction.inter_3997 c row := by
    simp only [KeccakfPermAir.extraction.inter_3999, KeccakfPermAir.extraction.inter_3998, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_3997 c row = (mc 1665 + mc 2462 - mc 2071*mc 2462 - 2*mc 1665*mc 2462 + 2*mc 1665*mc 2071*mc 2462) + 2 * KeccakfPermAir.extraction.inter_3995 c row := by
    simp only [KeccakfPermAir.extraction.inter_3997, KeccakfPermAir.extraction.inter_3996, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_3995 c row = (mc 1666 + mc 2463 - mc 2072*mc 2463 - 2*mc 1666*mc 2463 + 2*mc 1666*mc 2072*mc 2463) + 2 * KeccakfPermAir.extraction.inter_3993 c row := by
    simp only [KeccakfPermAir.extraction.inter_3995, KeccakfPermAir.extraction.inter_3994, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_3993 c row = (mc 1667 + mc 2464 - mc 2073*mc 2464 - 2*mc 1667*mc 2464 + 2*mc 1667*mc 2073*mc 2464) + 2 * KeccakfPermAir.extraction.inter_3991 c row := by
    simp only [KeccakfPermAir.extraction.inter_3993, KeccakfPermAir.extraction.inter_3992, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_3991 c row = (mc 1668 + mc 2401 - mc 2074*mc 2401 - 2*mc 1668*mc 2401 + 2*mc 1668*mc 2074*mc 2401) + 2 * KeccakfPermAir.extraction.inter_3989 c row := by
    simp only [KeccakfPermAir.extraction.inter_3991, KeccakfPermAir.extraction.inter_3990, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_3989 c row = (mc 1669 + mc 2402 - mc 2075*mc 2402 - 2*mc 1669*mc 2402 + 2*mc 1669*mc 2075*mc 2402) := by
    simp only [KeccakfPermAir.extraction.inter_3989, KeccakfPermAir.extraction.inter_3988, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2919 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2919 c row) :
    ((mc 1670 + mc 2403 - mc 2076*mc 2403 - 2*mc 1670*mc 2403 + 2*mc 1670*mc 2076*mc 2403) + 2*(mc 1671 + mc 2404 - mc 2077*mc 2404 - 2*mc 1671*mc 2404 + 2*mc 1671*mc 2077*mc 2404) + 4*(mc 1672 + mc 2405 - mc 2078*mc 2405 - 2*mc 1672*mc 2405 + 2*mc 1672*mc 2078*mc 2405) + 8*(mc 1673 + mc 2406 - mc 2079*mc 2406 - 2*mc 1673*mc 2406 + 2*mc 1673*mc 2079*mc 2406) + 16*(mc 1674 + mc 2407 - mc 2080*mc 2407 - 2*mc 1674*mc 2407 + 2*mc 1674*mc 2080*mc 2407) + 32*(mc 1675 + mc 2408 - mc 2017*mc 2408 - 2*mc 1675*mc 2408 + 2*mc 1675*mc 2017*mc 2408) + 64*(mc 1676 + mc 2409 - mc 2018*mc 2409 - 2*mc 1676*mc 2409 + 2*mc 1676*mc 2018*mc 2409) + 128*(mc 1677 + mc 2410 - mc 2019*mc 2410 - 2*mc 1677*mc 2410 + 2*mc 1677*mc 2019*mc 2410) + 256*(mc 1678 + mc 2411 - mc 2020*mc 2411 - 2*mc 1678*mc 2411 + 2*mc 1678*mc 2020*mc 2411) + 512*(mc 1679 + mc 2412 - mc 2021*mc 2412 - 2*mc 1679*mc 2412 + 2*mc 1679*mc 2021*mc 2412) + 1024*(mc 1680 + mc 2413 - mc 2022*mc 2413 - 2*mc 1680*mc 2413 + 2*mc 1680*mc 2022*mc 2413) + 2048*(mc 1681 + mc 2414 - mc 2023*mc 2414 - 2*mc 1681*mc 2414 + 2*mc 1681*mc 2023*mc 2414) + 4096*(mc 1682 + mc 2415 - mc 2024*mc 2415 - 2*mc 1682*mc 2415 + 2*mc 1682*mc 2024*mc 2415) + 8192*(mc 1683 + mc 2416 - mc 2025*mc 2416 - 2*mc 1683*mc 2416 + 2*mc 1683*mc 2025*mc 2416) + 16384*(mc 1684 + mc 2417 - mc 2026*mc 2417 - 2*mc 1684*mc 2417 + 2*mc 1684*mc 2026*mc 2417) + 32768*(mc 1685 + mc 2418 - mc 2027*mc 2418 - 2*mc 1685*mc 2418 + 2*mc 1685*mc 2027*mc 2418)) - mc 2474 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2919, KeccakfPermAir.extraction.inter_4049, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4048 c row = (mc 1671 + mc 2404 - mc 2077*mc 2404 - 2*mc 1671*mc 2404 + 2*mc 1671*mc 2077*mc 2404) + 2 * KeccakfPermAir.extraction.inter_4046 c row := by
    simp only [KeccakfPermAir.extraction.inter_4048, KeccakfPermAir.extraction.inter_4047, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4046 c row = (mc 1672 + mc 2405 - mc 2078*mc 2405 - 2*mc 1672*mc 2405 + 2*mc 1672*mc 2078*mc 2405) + 2 * KeccakfPermAir.extraction.inter_4044 c row := by
    simp only [KeccakfPermAir.extraction.inter_4046, KeccakfPermAir.extraction.inter_4045, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4044 c row = (mc 1673 + mc 2406 - mc 2079*mc 2406 - 2*mc 1673*mc 2406 + 2*mc 1673*mc 2079*mc 2406) + 2 * KeccakfPermAir.extraction.inter_4042 c row := by
    simp only [KeccakfPermAir.extraction.inter_4044, KeccakfPermAir.extraction.inter_4043, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4042 c row = (mc 1674 + mc 2407 - mc 2080*mc 2407 - 2*mc 1674*mc 2407 + 2*mc 1674*mc 2080*mc 2407) + 2 * KeccakfPermAir.extraction.inter_4040 c row := by
    simp only [KeccakfPermAir.extraction.inter_4042, KeccakfPermAir.extraction.inter_4041, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4040 c row = (mc 1675 + mc 2408 - mc 2017*mc 2408 - 2*mc 1675*mc 2408 + 2*mc 1675*mc 2017*mc 2408) + 2 * KeccakfPermAir.extraction.inter_4038 c row := by
    simp only [KeccakfPermAir.extraction.inter_4040, KeccakfPermAir.extraction.inter_4039, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4038 c row = (mc 1676 + mc 2409 - mc 2018*mc 2409 - 2*mc 1676*mc 2409 + 2*mc 1676*mc 2018*mc 2409) + 2 * KeccakfPermAir.extraction.inter_4036 c row := by
    simp only [KeccakfPermAir.extraction.inter_4038, KeccakfPermAir.extraction.inter_4037, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4036 c row = (mc 1677 + mc 2410 - mc 2019*mc 2410 - 2*mc 1677*mc 2410 + 2*mc 1677*mc 2019*mc 2410) + 2 * KeccakfPermAir.extraction.inter_4034 c row := by
    simp only [KeccakfPermAir.extraction.inter_4036, KeccakfPermAir.extraction.inter_4035, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4034 c row = (mc 1678 + mc 2411 - mc 2020*mc 2411 - 2*mc 1678*mc 2411 + 2*mc 1678*mc 2020*mc 2411) + 2 * KeccakfPermAir.extraction.inter_4032 c row := by
    simp only [KeccakfPermAir.extraction.inter_4034, KeccakfPermAir.extraction.inter_4033, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4032 c row = (mc 1679 + mc 2412 - mc 2021*mc 2412 - 2*mc 1679*mc 2412 + 2*mc 1679*mc 2021*mc 2412) + 2 * KeccakfPermAir.extraction.inter_4030 c row := by
    simp only [KeccakfPermAir.extraction.inter_4032, KeccakfPermAir.extraction.inter_4031, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4030 c row = (mc 1680 + mc 2413 - mc 2022*mc 2413 - 2*mc 1680*mc 2413 + 2*mc 1680*mc 2022*mc 2413) + 2 * KeccakfPermAir.extraction.inter_4028 c row := by
    simp only [KeccakfPermAir.extraction.inter_4030, KeccakfPermAir.extraction.inter_4029, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4028 c row = (mc 1681 + mc 2414 - mc 2023*mc 2414 - 2*mc 1681*mc 2414 + 2*mc 1681*mc 2023*mc 2414) + 2 * KeccakfPermAir.extraction.inter_4026 c row := by
    simp only [KeccakfPermAir.extraction.inter_4028, KeccakfPermAir.extraction.inter_4027, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4026 c row = (mc 1682 + mc 2415 - mc 2024*mc 2415 - 2*mc 1682*mc 2415 + 2*mc 1682*mc 2024*mc 2415) + 2 * KeccakfPermAir.extraction.inter_4024 c row := by
    simp only [KeccakfPermAir.extraction.inter_4026, KeccakfPermAir.extraction.inter_4025, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4024 c row = (mc 1683 + mc 2416 - mc 2025*mc 2416 - 2*mc 1683*mc 2416 + 2*mc 1683*mc 2025*mc 2416) + 2 * KeccakfPermAir.extraction.inter_4022 c row := by
    simp only [KeccakfPermAir.extraction.inter_4024, KeccakfPermAir.extraction.inter_4023, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4022 c row = (mc 1684 + mc 2417 - mc 2026*mc 2417 - 2*mc 1684*mc 2417 + 2*mc 1684*mc 2026*mc 2417) + 2 * KeccakfPermAir.extraction.inter_4020 c row := by
    simp only [KeccakfPermAir.extraction.inter_4022, KeccakfPermAir.extraction.inter_4021, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4020 c row = (mc 1685 + mc 2418 - mc 2027*mc 2418 - 2*mc 1685*mc 2418 + 2*mc 1685*mc 2027*mc 2418) := by
    simp only [KeccakfPermAir.extraction.inter_4020, KeccakfPermAir.extraction.inter_4019, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2920 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2920 c row) :
    ((mc 1686 + mc 2419 - mc 2028*mc 2419 - 2*mc 1686*mc 2419 + 2*mc 1686*mc 2028*mc 2419) + 2*(mc 1687 + mc 2420 - mc 2029*mc 2420 - 2*mc 1687*mc 2420 + 2*mc 1687*mc 2029*mc 2420) + 4*(mc 1688 + mc 2421 - mc 2030*mc 2421 - 2*mc 1688*mc 2421 + 2*mc 1688*mc 2030*mc 2421) + 8*(mc 1689 + mc 2422 - mc 2031*mc 2422 - 2*mc 1689*mc 2422 + 2*mc 1689*mc 2031*mc 2422) + 16*(mc 1690 + mc 2423 - mc 2032*mc 2423 - 2*mc 1690*mc 2423 + 2*mc 1690*mc 2032*mc 2423) + 32*(mc 1691 + mc 2424 - mc 2033*mc 2424 - 2*mc 1691*mc 2424 + 2*mc 1691*mc 2033*mc 2424) + 64*(mc 1692 + mc 2425 - mc 2034*mc 2425 - 2*mc 1692*mc 2425 + 2*mc 1692*mc 2034*mc 2425) + 128*(mc 1693 + mc 2426 - mc 2035*mc 2426 - 2*mc 1693*mc 2426 + 2*mc 1693*mc 2035*mc 2426) + 256*(mc 1694 + mc 2427 - mc 2036*mc 2427 - 2*mc 1694*mc 2427 + 2*mc 1694*mc 2036*mc 2427) + 512*(mc 1695 + mc 2428 - mc 2037*mc 2428 - 2*mc 1695*mc 2428 + 2*mc 1695*mc 2037*mc 2428) + 1024*(mc 1696 + mc 2429 - mc 2038*mc 2429 - 2*mc 1696*mc 2429 + 2*mc 1696*mc 2038*mc 2429) + 2048*(mc 1633 + mc 2430 - mc 2039*mc 2430 - 2*mc 1633*mc 2430 + 2*mc 1633*mc 2039*mc 2430) + 4096*(mc 1634 + mc 2431 - mc 2040*mc 2431 - 2*mc 1634*mc 2431 + 2*mc 1634*mc 2040*mc 2431) + 8192*(mc 1635 + mc 2432 - mc 2041*mc 2432 - 2*mc 1635*mc 2432 + 2*mc 1635*mc 2041*mc 2432) + 16384*(mc 1636 + mc 2433 - mc 2042*mc 2433 - 2*mc 1636*mc 2433 + 2*mc 1636*mc 2042*mc 2433) + 32768*(mc 1637 + mc 2434 - mc 2043*mc 2434 - 2*mc 1637*mc 2434 + 2*mc 1637*mc 2043*mc 2434)) - mc 2475 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2920, KeccakfPermAir.extraction.inter_4080, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4079 c row = (mc 1687 + mc 2420 - mc 2029*mc 2420 - 2*mc 1687*mc 2420 + 2*mc 1687*mc 2029*mc 2420) + 2 * KeccakfPermAir.extraction.inter_4077 c row := by
    simp only [KeccakfPermAir.extraction.inter_4079, KeccakfPermAir.extraction.inter_4078, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4077 c row = (mc 1688 + mc 2421 - mc 2030*mc 2421 - 2*mc 1688*mc 2421 + 2*mc 1688*mc 2030*mc 2421) + 2 * KeccakfPermAir.extraction.inter_4075 c row := by
    simp only [KeccakfPermAir.extraction.inter_4077, KeccakfPermAir.extraction.inter_4076, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4075 c row = (mc 1689 + mc 2422 - mc 2031*mc 2422 - 2*mc 1689*mc 2422 + 2*mc 1689*mc 2031*mc 2422) + 2 * KeccakfPermAir.extraction.inter_4073 c row := by
    simp only [KeccakfPermAir.extraction.inter_4075, KeccakfPermAir.extraction.inter_4074, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4073 c row = (mc 1690 + mc 2423 - mc 2032*mc 2423 - 2*mc 1690*mc 2423 + 2*mc 1690*mc 2032*mc 2423) + 2 * KeccakfPermAir.extraction.inter_4071 c row := by
    simp only [KeccakfPermAir.extraction.inter_4073, KeccakfPermAir.extraction.inter_4072, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4071 c row = (mc 1691 + mc 2424 - mc 2033*mc 2424 - 2*mc 1691*mc 2424 + 2*mc 1691*mc 2033*mc 2424) + 2 * KeccakfPermAir.extraction.inter_4069 c row := by
    simp only [KeccakfPermAir.extraction.inter_4071, KeccakfPermAir.extraction.inter_4070, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4069 c row = (mc 1692 + mc 2425 - mc 2034*mc 2425 - 2*mc 1692*mc 2425 + 2*mc 1692*mc 2034*mc 2425) + 2 * KeccakfPermAir.extraction.inter_4067 c row := by
    simp only [KeccakfPermAir.extraction.inter_4069, KeccakfPermAir.extraction.inter_4068, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4067 c row = (mc 1693 + mc 2426 - mc 2035*mc 2426 - 2*mc 1693*mc 2426 + 2*mc 1693*mc 2035*mc 2426) + 2 * KeccakfPermAir.extraction.inter_4065 c row := by
    simp only [KeccakfPermAir.extraction.inter_4067, KeccakfPermAir.extraction.inter_4066, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4065 c row = (mc 1694 + mc 2427 - mc 2036*mc 2427 - 2*mc 1694*mc 2427 + 2*mc 1694*mc 2036*mc 2427) + 2 * KeccakfPermAir.extraction.inter_4063 c row := by
    simp only [KeccakfPermAir.extraction.inter_4065, KeccakfPermAir.extraction.inter_4064, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4063 c row = (mc 1695 + mc 2428 - mc 2037*mc 2428 - 2*mc 1695*mc 2428 + 2*mc 1695*mc 2037*mc 2428) + 2 * KeccakfPermAir.extraction.inter_4061 c row := by
    simp only [KeccakfPermAir.extraction.inter_4063, KeccakfPermAir.extraction.inter_4062, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4061 c row = (mc 1696 + mc 2429 - mc 2038*mc 2429 - 2*mc 1696*mc 2429 + 2*mc 1696*mc 2038*mc 2429) + 2 * KeccakfPermAir.extraction.inter_4059 c row := by
    simp only [KeccakfPermAir.extraction.inter_4061, KeccakfPermAir.extraction.inter_4060, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4059 c row = (mc 1633 + mc 2430 - mc 2039*mc 2430 - 2*mc 1633*mc 2430 + 2*mc 1633*mc 2039*mc 2430) + 2 * KeccakfPermAir.extraction.inter_4057 c row := by
    simp only [KeccakfPermAir.extraction.inter_4059, KeccakfPermAir.extraction.inter_4058, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4057 c row = (mc 1634 + mc 2431 - mc 2040*mc 2431 - 2*mc 1634*mc 2431 + 2*mc 1634*mc 2040*mc 2431) + 2 * KeccakfPermAir.extraction.inter_4055 c row := by
    simp only [KeccakfPermAir.extraction.inter_4057, KeccakfPermAir.extraction.inter_4056, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4055 c row = (mc 1635 + mc 2432 - mc 2041*mc 2432 - 2*mc 1635*mc 2432 + 2*mc 1635*mc 2041*mc 2432) + 2 * KeccakfPermAir.extraction.inter_4053 c row := by
    simp only [KeccakfPermAir.extraction.inter_4055, KeccakfPermAir.extraction.inter_4054, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4053 c row = (mc 1636 + mc 2433 - mc 2042*mc 2433 - 2*mc 1636*mc 2433 + 2*mc 1636*mc 2042*mc 2433) + 2 * KeccakfPermAir.extraction.inter_4051 c row := by
    simp only [KeccakfPermAir.extraction.inter_4053, KeccakfPermAir.extraction.inter_4052, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4051 c row = (mc 1637 + mc 2434 - mc 2043*mc 2434 - 2*mc 1637*mc 2434 + 2*mc 1637*mc 2043*mc 2434) := by
    simp only [KeccakfPermAir.extraction.inter_4051, KeccakfPermAir.extraction.inter_4050, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2921 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2921 c row) :
    ((mc 1638 + mc 2435 - mc 2044*mc 2435 - 2*mc 1638*mc 2435 + 2*mc 1638*mc 2044*mc 2435) + 2*(mc 1639 + mc 2436 - mc 2045*mc 2436 - 2*mc 1639*mc 2436 + 2*mc 1639*mc 2045*mc 2436) + 4*(mc 1640 + mc 2437 - mc 2046*mc 2437 - 2*mc 1640*mc 2437 + 2*mc 1640*mc 2046*mc 2437) + 8*(mc 1641 + mc 2438 - mc 2047*mc 2438 - 2*mc 1641*mc 2438 + 2*mc 1641*mc 2047*mc 2438) + 16*(mc 1642 + mc 2439 - mc 2048*mc 2439 - 2*mc 1642*mc 2439 + 2*mc 1642*mc 2048*mc 2439) + 32*(mc 1643 + mc 2440 - mc 2049*mc 2440 - 2*mc 1643*mc 2440 + 2*mc 1643*mc 2049*mc 2440) + 64*(mc 1644 + mc 2441 - mc 2050*mc 2441 - 2*mc 1644*mc 2441 + 2*mc 1644*mc 2050*mc 2441) + 128*(mc 1645 + mc 2442 - mc 2051*mc 2442 - 2*mc 1645*mc 2442 + 2*mc 1645*mc 2051*mc 2442) + 256*(mc 1646 + mc 2443 - mc 2052*mc 2443 - 2*mc 1646*mc 2443 + 2*mc 1646*mc 2052*mc 2443) + 512*(mc 1647 + mc 2444 - mc 2053*mc 2444 - 2*mc 1647*mc 2444 + 2*mc 1647*mc 2053*mc 2444) + 1024*(mc 1648 + mc 2445 - mc 2054*mc 2445 - 2*mc 1648*mc 2445 + 2*mc 1648*mc 2054*mc 2445) + 2048*(mc 1649 + mc 2446 - mc 2055*mc 2446 - 2*mc 1649*mc 2446 + 2*mc 1649*mc 2055*mc 2446) + 4096*(mc 1650 + mc 2447 - mc 2056*mc 2447 - 2*mc 1650*mc 2447 + 2*mc 1650*mc 2056*mc 2447) + 8192*(mc 1651 + mc 2448 - mc 2057*mc 2448 - 2*mc 1651*mc 2448 + 2*mc 1651*mc 2057*mc 2448) + 16384*(mc 1652 + mc 2449 - mc 2058*mc 2449 - 2*mc 1652*mc 2449 + 2*mc 1652*mc 2058*mc 2449) + 32768*(mc 1653 + mc 2450 - mc 2059*mc 2450 - 2*mc 1653*mc 2450 + 2*mc 1653*mc 2059*mc 2450)) - mc 2476 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2921, KeccakfPermAir.extraction.inter_4111, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4110 c row = (mc 1639 + mc 2436 - mc 2045*mc 2436 - 2*mc 1639*mc 2436 + 2*mc 1639*mc 2045*mc 2436) + 2 * KeccakfPermAir.extraction.inter_4108 c row := by
    simp only [KeccakfPermAir.extraction.inter_4110, KeccakfPermAir.extraction.inter_4109, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4108 c row = (mc 1640 + mc 2437 - mc 2046*mc 2437 - 2*mc 1640*mc 2437 + 2*mc 1640*mc 2046*mc 2437) + 2 * KeccakfPermAir.extraction.inter_4106 c row := by
    simp only [KeccakfPermAir.extraction.inter_4108, KeccakfPermAir.extraction.inter_4107, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4106 c row = (mc 1641 + mc 2438 - mc 2047*mc 2438 - 2*mc 1641*mc 2438 + 2*mc 1641*mc 2047*mc 2438) + 2 * KeccakfPermAir.extraction.inter_4104 c row := by
    simp only [KeccakfPermAir.extraction.inter_4106, KeccakfPermAir.extraction.inter_4105, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4104 c row = (mc 1642 + mc 2439 - mc 2048*mc 2439 - 2*mc 1642*mc 2439 + 2*mc 1642*mc 2048*mc 2439) + 2 * KeccakfPermAir.extraction.inter_4102 c row := by
    simp only [KeccakfPermAir.extraction.inter_4104, KeccakfPermAir.extraction.inter_4103, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4102 c row = (mc 1643 + mc 2440 - mc 2049*mc 2440 - 2*mc 1643*mc 2440 + 2*mc 1643*mc 2049*mc 2440) + 2 * KeccakfPermAir.extraction.inter_4100 c row := by
    simp only [KeccakfPermAir.extraction.inter_4102, KeccakfPermAir.extraction.inter_4101, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4100 c row = (mc 1644 + mc 2441 - mc 2050*mc 2441 - 2*mc 1644*mc 2441 + 2*mc 1644*mc 2050*mc 2441) + 2 * KeccakfPermAir.extraction.inter_4098 c row := by
    simp only [KeccakfPermAir.extraction.inter_4100, KeccakfPermAir.extraction.inter_4099, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4098 c row = (mc 1645 + mc 2442 - mc 2051*mc 2442 - 2*mc 1645*mc 2442 + 2*mc 1645*mc 2051*mc 2442) + 2 * KeccakfPermAir.extraction.inter_4096 c row := by
    simp only [KeccakfPermAir.extraction.inter_4098, KeccakfPermAir.extraction.inter_4097, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4096 c row = (mc 1646 + mc 2443 - mc 2052*mc 2443 - 2*mc 1646*mc 2443 + 2*mc 1646*mc 2052*mc 2443) + 2 * KeccakfPermAir.extraction.inter_4094 c row := by
    simp only [KeccakfPermAir.extraction.inter_4096, KeccakfPermAir.extraction.inter_4095, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4094 c row = (mc 1647 + mc 2444 - mc 2053*mc 2444 - 2*mc 1647*mc 2444 + 2*mc 1647*mc 2053*mc 2444) + 2 * KeccakfPermAir.extraction.inter_4092 c row := by
    simp only [KeccakfPermAir.extraction.inter_4094, KeccakfPermAir.extraction.inter_4093, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4092 c row = (mc 1648 + mc 2445 - mc 2054*mc 2445 - 2*mc 1648*mc 2445 + 2*mc 1648*mc 2054*mc 2445) + 2 * KeccakfPermAir.extraction.inter_4090 c row := by
    simp only [KeccakfPermAir.extraction.inter_4092, KeccakfPermAir.extraction.inter_4091, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4090 c row = (mc 1649 + mc 2446 - mc 2055*mc 2446 - 2*mc 1649*mc 2446 + 2*mc 1649*mc 2055*mc 2446) + 2 * KeccakfPermAir.extraction.inter_4088 c row := by
    simp only [KeccakfPermAir.extraction.inter_4090, KeccakfPermAir.extraction.inter_4089, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4088 c row = (mc 1650 + mc 2447 - mc 2056*mc 2447 - 2*mc 1650*mc 2447 + 2*mc 1650*mc 2056*mc 2447) + 2 * KeccakfPermAir.extraction.inter_4086 c row := by
    simp only [KeccakfPermAir.extraction.inter_4088, KeccakfPermAir.extraction.inter_4087, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4086 c row = (mc 1651 + mc 2448 - mc 2057*mc 2448 - 2*mc 1651*mc 2448 + 2*mc 1651*mc 2057*mc 2448) + 2 * KeccakfPermAir.extraction.inter_4084 c row := by
    simp only [KeccakfPermAir.extraction.inter_4086, KeccakfPermAir.extraction.inter_4085, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4084 c row = (mc 1652 + mc 2449 - mc 2058*mc 2449 - 2*mc 1652*mc 2449 + 2*mc 1652*mc 2058*mc 2449) + 2 * KeccakfPermAir.extraction.inter_4082 c row := by
    simp only [KeccakfPermAir.extraction.inter_4084, KeccakfPermAir.extraction.inter_4083, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4082 c row = (mc 1653 + mc 2450 - mc 2059*mc 2450 - 2*mc 1653*mc 2450 + 2*mc 1653*mc 2059*mc 2450) := by
    simp only [KeccakfPermAir.extraction.inter_4082, KeccakfPermAir.extraction.inter_4081, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2922 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2922 c row) :
    ((mc 2060 + mc 865 - mc 2451*mc 865 - 2*mc 2060*mc 865 + 2*mc 2060*mc 2451*mc 865) + 2*(mc 2061 + mc 866 - mc 2452*mc 866 - 2*mc 2061*mc 866 + 2*mc 2061*mc 2452*mc 866) + 4*(mc 2062 + mc 867 - mc 2453*mc 867 - 2*mc 2062*mc 867 + 2*mc 2062*mc 2453*mc 867) + 8*(mc 2063 + mc 868 - mc 2454*mc 868 - 2*mc 2063*mc 868 + 2*mc 2063*mc 2454*mc 868) + 16*(mc 2064 + mc 869 - mc 2455*mc 869 - 2*mc 2064*mc 869 + 2*mc 2064*mc 2455*mc 869) + 32*(mc 2065 + mc 870 - mc 2456*mc 870 - 2*mc 2065*mc 870 + 2*mc 2065*mc 2456*mc 870) + 64*(mc 2066 + mc 871 - mc 2457*mc 871 - 2*mc 2066*mc 871 + 2*mc 2066*mc 2457*mc 871) + 128*(mc 2067 + mc 872 - mc 2458*mc 872 - 2*mc 2067*mc 872 + 2*mc 2067*mc 2458*mc 872) + 256*(mc 2068 + mc 873 - mc 2459*mc 873 - 2*mc 2068*mc 873 + 2*mc 2068*mc 2459*mc 873) + 512*(mc 2069 + mc 874 - mc 2460*mc 874 - 2*mc 2069*mc 874 + 2*mc 2069*mc 2460*mc 874) + 1024*(mc 2070 + mc 875 - mc 2461*mc 875 - 2*mc 2070*mc 875 + 2*mc 2070*mc 2461*mc 875) + 2048*(mc 2071 + mc 876 - mc 2462*mc 876 - 2*mc 2071*mc 876 + 2*mc 2071*mc 2462*mc 876) + 4096*(mc 2072 + mc 877 - mc 2463*mc 877 - 2*mc 2072*mc 877 + 2*mc 2072*mc 2463*mc 877) + 8192*(mc 2073 + mc 878 - mc 2464*mc 878 - 2*mc 2073*mc 878 + 2*mc 2073*mc 2464*mc 878) + 16384*(mc 2074 + mc 879 - mc 2401*mc 879 - 2*mc 2074*mc 879 + 2*mc 2074*mc 2401*mc 879) + 32768*(mc 2075 + mc 880 - mc 2402*mc 880 - 2*mc 2075*mc 880 + 2*mc 2075*mc 2402*mc 880)) - mc 2477 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2922, KeccakfPermAir.extraction.inter_4142, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4141 c row = (mc 2061 + mc 866 - mc 2452*mc 866 - 2*mc 2061*mc 866 + 2*mc 2061*mc 2452*mc 866) + 2 * KeccakfPermAir.extraction.inter_4139 c row := by
    simp only [KeccakfPermAir.extraction.inter_4141, KeccakfPermAir.extraction.inter_4140, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4139 c row = (mc 2062 + mc 867 - mc 2453*mc 867 - 2*mc 2062*mc 867 + 2*mc 2062*mc 2453*mc 867) + 2 * KeccakfPermAir.extraction.inter_4137 c row := by
    simp only [KeccakfPermAir.extraction.inter_4139, KeccakfPermAir.extraction.inter_4138, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4137 c row = (mc 2063 + mc 868 - mc 2454*mc 868 - 2*mc 2063*mc 868 + 2*mc 2063*mc 2454*mc 868) + 2 * KeccakfPermAir.extraction.inter_4135 c row := by
    simp only [KeccakfPermAir.extraction.inter_4137, KeccakfPermAir.extraction.inter_4136, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4135 c row = (mc 2064 + mc 869 - mc 2455*mc 869 - 2*mc 2064*mc 869 + 2*mc 2064*mc 2455*mc 869) + 2 * KeccakfPermAir.extraction.inter_4133 c row := by
    simp only [KeccakfPermAir.extraction.inter_4135, KeccakfPermAir.extraction.inter_4134, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4133 c row = (mc 2065 + mc 870 - mc 2456*mc 870 - 2*mc 2065*mc 870 + 2*mc 2065*mc 2456*mc 870) + 2 * KeccakfPermAir.extraction.inter_4131 c row := by
    simp only [KeccakfPermAir.extraction.inter_4133, KeccakfPermAir.extraction.inter_4132, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4131 c row = (mc 2066 + mc 871 - mc 2457*mc 871 - 2*mc 2066*mc 871 + 2*mc 2066*mc 2457*mc 871) + 2 * KeccakfPermAir.extraction.inter_4129 c row := by
    simp only [KeccakfPermAir.extraction.inter_4131, KeccakfPermAir.extraction.inter_4130, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4129 c row = (mc 2067 + mc 872 - mc 2458*mc 872 - 2*mc 2067*mc 872 + 2*mc 2067*mc 2458*mc 872) + 2 * KeccakfPermAir.extraction.inter_4127 c row := by
    simp only [KeccakfPermAir.extraction.inter_4129, KeccakfPermAir.extraction.inter_4128, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4127 c row = (mc 2068 + mc 873 - mc 2459*mc 873 - 2*mc 2068*mc 873 + 2*mc 2068*mc 2459*mc 873) + 2 * KeccakfPermAir.extraction.inter_4125 c row := by
    simp only [KeccakfPermAir.extraction.inter_4127, KeccakfPermAir.extraction.inter_4126, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4125 c row = (mc 2069 + mc 874 - mc 2460*mc 874 - 2*mc 2069*mc 874 + 2*mc 2069*mc 2460*mc 874) + 2 * KeccakfPermAir.extraction.inter_4123 c row := by
    simp only [KeccakfPermAir.extraction.inter_4125, KeccakfPermAir.extraction.inter_4124, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4123 c row = (mc 2070 + mc 875 - mc 2461*mc 875 - 2*mc 2070*mc 875 + 2*mc 2070*mc 2461*mc 875) + 2 * KeccakfPermAir.extraction.inter_4121 c row := by
    simp only [KeccakfPermAir.extraction.inter_4123, KeccakfPermAir.extraction.inter_4122, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4121 c row = (mc 2071 + mc 876 - mc 2462*mc 876 - 2*mc 2071*mc 876 + 2*mc 2071*mc 2462*mc 876) + 2 * KeccakfPermAir.extraction.inter_4119 c row := by
    simp only [KeccakfPermAir.extraction.inter_4121, KeccakfPermAir.extraction.inter_4120, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4119 c row = (mc 2072 + mc 877 - mc 2463*mc 877 - 2*mc 2072*mc 877 + 2*mc 2072*mc 2463*mc 877) + 2 * KeccakfPermAir.extraction.inter_4117 c row := by
    simp only [KeccakfPermAir.extraction.inter_4119, KeccakfPermAir.extraction.inter_4118, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4117 c row = (mc 2073 + mc 878 - mc 2464*mc 878 - 2*mc 2073*mc 878 + 2*mc 2073*mc 2464*mc 878) + 2 * KeccakfPermAir.extraction.inter_4115 c row := by
    simp only [KeccakfPermAir.extraction.inter_4117, KeccakfPermAir.extraction.inter_4116, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4115 c row = (mc 2074 + mc 879 - mc 2401*mc 879 - 2*mc 2074*mc 879 + 2*mc 2074*mc 2401*mc 879) + 2 * KeccakfPermAir.extraction.inter_4113 c row := by
    simp only [KeccakfPermAir.extraction.inter_4115, KeccakfPermAir.extraction.inter_4114, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4113 c row = (mc 2075 + mc 880 - mc 2402*mc 880 - 2*mc 2075*mc 880 + 2*mc 2075*mc 2402*mc 880) := by
    simp only [KeccakfPermAir.extraction.inter_4113, KeccakfPermAir.extraction.inter_4112, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2923 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2923 c row) :
    ((mc 2076 + mc 881 - mc 2403*mc 881 - 2*mc 2076*mc 881 + 2*mc 2076*mc 2403*mc 881) + 2*(mc 2077 + mc 882 - mc 2404*mc 882 - 2*mc 2077*mc 882 + 2*mc 2077*mc 2404*mc 882) + 4*(mc 2078 + mc 883 - mc 2405*mc 883 - 2*mc 2078*mc 883 + 2*mc 2078*mc 2405*mc 883) + 8*(mc 2079 + mc 884 - mc 2406*mc 884 - 2*mc 2079*mc 884 + 2*mc 2079*mc 2406*mc 884) + 16*(mc 2080 + mc 885 - mc 2407*mc 885 - 2*mc 2080*mc 885 + 2*mc 2080*mc 2407*mc 885) + 32*(mc 2017 + mc 886 - mc 2408*mc 886 - 2*mc 2017*mc 886 + 2*mc 2017*mc 2408*mc 886) + 64*(mc 2018 + mc 887 - mc 2409*mc 887 - 2*mc 2018*mc 887 + 2*mc 2018*mc 2409*mc 887) + 128*(mc 2019 + mc 888 - mc 2410*mc 888 - 2*mc 2019*mc 888 + 2*mc 2019*mc 2410*mc 888) + 256*(mc 2020 + mc 889 - mc 2411*mc 889 - 2*mc 2020*mc 889 + 2*mc 2020*mc 2411*mc 889) + 512*(mc 2021 + mc 890 - mc 2412*mc 890 - 2*mc 2021*mc 890 + 2*mc 2021*mc 2412*mc 890) + 1024*(mc 2022 + mc 891 - mc 2413*mc 891 - 2*mc 2022*mc 891 + 2*mc 2022*mc 2413*mc 891) + 2048*(mc 2023 + mc 892 - mc 2414*mc 892 - 2*mc 2023*mc 892 + 2*mc 2023*mc 2414*mc 892) + 4096*(mc 2024 + mc 893 - mc 2415*mc 893 - 2*mc 2024*mc 893 + 2*mc 2024*mc 2415*mc 893) + 8192*(mc 2025 + mc 894 - mc 2416*mc 894 - 2*mc 2025*mc 894 + 2*mc 2025*mc 2416*mc 894) + 16384*(mc 2026 + mc 895 - mc 2417*mc 895 - 2*mc 2026*mc 895 + 2*mc 2026*mc 2417*mc 895) + 32768*(mc 2027 + mc 896 - mc 2418*mc 896 - 2*mc 2027*mc 896 + 2*mc 2027*mc 2418*mc 896)) - mc 2478 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2923, KeccakfPermAir.extraction.inter_4173, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4172 c row = (mc 2077 + mc 882 - mc 2404*mc 882 - 2*mc 2077*mc 882 + 2*mc 2077*mc 2404*mc 882) + 2 * KeccakfPermAir.extraction.inter_4170 c row := by
    simp only [KeccakfPermAir.extraction.inter_4172, KeccakfPermAir.extraction.inter_4171, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4170 c row = (mc 2078 + mc 883 - mc 2405*mc 883 - 2*mc 2078*mc 883 + 2*mc 2078*mc 2405*mc 883) + 2 * KeccakfPermAir.extraction.inter_4168 c row := by
    simp only [KeccakfPermAir.extraction.inter_4170, KeccakfPermAir.extraction.inter_4169, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4168 c row = (mc 2079 + mc 884 - mc 2406*mc 884 - 2*mc 2079*mc 884 + 2*mc 2079*mc 2406*mc 884) + 2 * KeccakfPermAir.extraction.inter_4166 c row := by
    simp only [KeccakfPermAir.extraction.inter_4168, KeccakfPermAir.extraction.inter_4167, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4166 c row = (mc 2080 + mc 885 - mc 2407*mc 885 - 2*mc 2080*mc 885 + 2*mc 2080*mc 2407*mc 885) + 2 * KeccakfPermAir.extraction.inter_4164 c row := by
    simp only [KeccakfPermAir.extraction.inter_4166, KeccakfPermAir.extraction.inter_4165, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4164 c row = (mc 2017 + mc 886 - mc 2408*mc 886 - 2*mc 2017*mc 886 + 2*mc 2017*mc 2408*mc 886) + 2 * KeccakfPermAir.extraction.inter_4162 c row := by
    simp only [KeccakfPermAir.extraction.inter_4164, KeccakfPermAir.extraction.inter_4163, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4162 c row = (mc 2018 + mc 887 - mc 2409*mc 887 - 2*mc 2018*mc 887 + 2*mc 2018*mc 2409*mc 887) + 2 * KeccakfPermAir.extraction.inter_4160 c row := by
    simp only [KeccakfPermAir.extraction.inter_4162, KeccakfPermAir.extraction.inter_4161, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4160 c row = (mc 2019 + mc 888 - mc 2410*mc 888 - 2*mc 2019*mc 888 + 2*mc 2019*mc 2410*mc 888) + 2 * KeccakfPermAir.extraction.inter_4158 c row := by
    simp only [KeccakfPermAir.extraction.inter_4160, KeccakfPermAir.extraction.inter_4159, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4158 c row = (mc 2020 + mc 889 - mc 2411*mc 889 - 2*mc 2020*mc 889 + 2*mc 2020*mc 2411*mc 889) + 2 * KeccakfPermAir.extraction.inter_4156 c row := by
    simp only [KeccakfPermAir.extraction.inter_4158, KeccakfPermAir.extraction.inter_4157, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4156 c row = (mc 2021 + mc 890 - mc 2412*mc 890 - 2*mc 2021*mc 890 + 2*mc 2021*mc 2412*mc 890) + 2 * KeccakfPermAir.extraction.inter_4154 c row := by
    simp only [KeccakfPermAir.extraction.inter_4156, KeccakfPermAir.extraction.inter_4155, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4154 c row = (mc 2022 + mc 891 - mc 2413*mc 891 - 2*mc 2022*mc 891 + 2*mc 2022*mc 2413*mc 891) + 2 * KeccakfPermAir.extraction.inter_4152 c row := by
    simp only [KeccakfPermAir.extraction.inter_4154, KeccakfPermAir.extraction.inter_4153, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4152 c row = (mc 2023 + mc 892 - mc 2414*mc 892 - 2*mc 2023*mc 892 + 2*mc 2023*mc 2414*mc 892) + 2 * KeccakfPermAir.extraction.inter_4150 c row := by
    simp only [KeccakfPermAir.extraction.inter_4152, KeccakfPermAir.extraction.inter_4151, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4150 c row = (mc 2024 + mc 893 - mc 2415*mc 893 - 2*mc 2024*mc 893 + 2*mc 2024*mc 2415*mc 893) + 2 * KeccakfPermAir.extraction.inter_4148 c row := by
    simp only [KeccakfPermAir.extraction.inter_4150, KeccakfPermAir.extraction.inter_4149, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4148 c row = (mc 2025 + mc 894 - mc 2416*mc 894 - 2*mc 2025*mc 894 + 2*mc 2025*mc 2416*mc 894) + 2 * KeccakfPermAir.extraction.inter_4146 c row := by
    simp only [KeccakfPermAir.extraction.inter_4148, KeccakfPermAir.extraction.inter_4147, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4146 c row = (mc 2026 + mc 895 - mc 2417*mc 895 - 2*mc 2026*mc 895 + 2*mc 2026*mc 2417*mc 895) + 2 * KeccakfPermAir.extraction.inter_4144 c row := by
    simp only [KeccakfPermAir.extraction.inter_4146, KeccakfPermAir.extraction.inter_4145, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4144 c row = (mc 2027 + mc 896 - mc 2418*mc 896 - 2*mc 2027*mc 896 + 2*mc 2027*mc 2418*mc 896) := by
    simp only [KeccakfPermAir.extraction.inter_4144, KeccakfPermAir.extraction.inter_4143, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2924 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2924 c row) :
    ((mc 2028 + mc 897 - mc 2419*mc 897 - 2*mc 2028*mc 897 + 2*mc 2028*mc 2419*mc 897) + 2*(mc 2029 + mc 898 - mc 2420*mc 898 - 2*mc 2029*mc 898 + 2*mc 2029*mc 2420*mc 898) + 4*(mc 2030 + mc 899 - mc 2421*mc 899 - 2*mc 2030*mc 899 + 2*mc 2030*mc 2421*mc 899) + 8*(mc 2031 + mc 900 - mc 2422*mc 900 - 2*mc 2031*mc 900 + 2*mc 2031*mc 2422*mc 900) + 16*(mc 2032 + mc 901 - mc 2423*mc 901 - 2*mc 2032*mc 901 + 2*mc 2032*mc 2423*mc 901) + 32*(mc 2033 + mc 902 - mc 2424*mc 902 - 2*mc 2033*mc 902 + 2*mc 2033*mc 2424*mc 902) + 64*(mc 2034 + mc 903 - mc 2425*mc 903 - 2*mc 2034*mc 903 + 2*mc 2034*mc 2425*mc 903) + 128*(mc 2035 + mc 904 - mc 2426*mc 904 - 2*mc 2035*mc 904 + 2*mc 2035*mc 2426*mc 904) + 256*(mc 2036 + mc 905 - mc 2427*mc 905 - 2*mc 2036*mc 905 + 2*mc 2036*mc 2427*mc 905) + 512*(mc 2037 + mc 906 - mc 2428*mc 906 - 2*mc 2037*mc 906 + 2*mc 2037*mc 2428*mc 906) + 1024*(mc 2038 + mc 907 - mc 2429*mc 907 - 2*mc 2038*mc 907 + 2*mc 2038*mc 2429*mc 907) + 2048*(mc 2039 + mc 908 - mc 2430*mc 908 - 2*mc 2039*mc 908 + 2*mc 2039*mc 2430*mc 908) + 4096*(mc 2040 + mc 909 - mc 2431*mc 909 - 2*mc 2040*mc 909 + 2*mc 2040*mc 2431*mc 909) + 8192*(mc 2041 + mc 910 - mc 2432*mc 910 - 2*mc 2041*mc 910 + 2*mc 2041*mc 2432*mc 910) + 16384*(mc 2042 + mc 911 - mc 2433*mc 911 - 2*mc 2042*mc 911 + 2*mc 2042*mc 2433*mc 911) + 32768*(mc 2043 + mc 912 - mc 2434*mc 912 - 2*mc 2043*mc 912 + 2*mc 2043*mc 2434*mc 912)) - mc 2479 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2924, KeccakfPermAir.extraction.inter_4204, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4203 c row = (mc 2029 + mc 898 - mc 2420*mc 898 - 2*mc 2029*mc 898 + 2*mc 2029*mc 2420*mc 898) + 2 * KeccakfPermAir.extraction.inter_4201 c row := by
    simp only [KeccakfPermAir.extraction.inter_4203, KeccakfPermAir.extraction.inter_4202, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4201 c row = (mc 2030 + mc 899 - mc 2421*mc 899 - 2*mc 2030*mc 899 + 2*mc 2030*mc 2421*mc 899) + 2 * KeccakfPermAir.extraction.inter_4199 c row := by
    simp only [KeccakfPermAir.extraction.inter_4201, KeccakfPermAir.extraction.inter_4200, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4199 c row = (mc 2031 + mc 900 - mc 2422*mc 900 - 2*mc 2031*mc 900 + 2*mc 2031*mc 2422*mc 900) + 2 * KeccakfPermAir.extraction.inter_4197 c row := by
    simp only [KeccakfPermAir.extraction.inter_4199, KeccakfPermAir.extraction.inter_4198, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4197 c row = (mc 2032 + mc 901 - mc 2423*mc 901 - 2*mc 2032*mc 901 + 2*mc 2032*mc 2423*mc 901) + 2 * KeccakfPermAir.extraction.inter_4195 c row := by
    simp only [KeccakfPermAir.extraction.inter_4197, KeccakfPermAir.extraction.inter_4196, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4195 c row = (mc 2033 + mc 902 - mc 2424*mc 902 - 2*mc 2033*mc 902 + 2*mc 2033*mc 2424*mc 902) + 2 * KeccakfPermAir.extraction.inter_4193 c row := by
    simp only [KeccakfPermAir.extraction.inter_4195, KeccakfPermAir.extraction.inter_4194, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4193 c row = (mc 2034 + mc 903 - mc 2425*mc 903 - 2*mc 2034*mc 903 + 2*mc 2034*mc 2425*mc 903) + 2 * KeccakfPermAir.extraction.inter_4191 c row := by
    simp only [KeccakfPermAir.extraction.inter_4193, KeccakfPermAir.extraction.inter_4192, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4191 c row = (mc 2035 + mc 904 - mc 2426*mc 904 - 2*mc 2035*mc 904 + 2*mc 2035*mc 2426*mc 904) + 2 * KeccakfPermAir.extraction.inter_4189 c row := by
    simp only [KeccakfPermAir.extraction.inter_4191, KeccakfPermAir.extraction.inter_4190, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4189 c row = (mc 2036 + mc 905 - mc 2427*mc 905 - 2*mc 2036*mc 905 + 2*mc 2036*mc 2427*mc 905) + 2 * KeccakfPermAir.extraction.inter_4187 c row := by
    simp only [KeccakfPermAir.extraction.inter_4189, KeccakfPermAir.extraction.inter_4188, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4187 c row = (mc 2037 + mc 906 - mc 2428*mc 906 - 2*mc 2037*mc 906 + 2*mc 2037*mc 2428*mc 906) + 2 * KeccakfPermAir.extraction.inter_4185 c row := by
    simp only [KeccakfPermAir.extraction.inter_4187, KeccakfPermAir.extraction.inter_4186, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4185 c row = (mc 2038 + mc 907 - mc 2429*mc 907 - 2*mc 2038*mc 907 + 2*mc 2038*mc 2429*mc 907) + 2 * KeccakfPermAir.extraction.inter_4183 c row := by
    simp only [KeccakfPermAir.extraction.inter_4185, KeccakfPermAir.extraction.inter_4184, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4183 c row = (mc 2039 + mc 908 - mc 2430*mc 908 - 2*mc 2039*mc 908 + 2*mc 2039*mc 2430*mc 908) + 2 * KeccakfPermAir.extraction.inter_4181 c row := by
    simp only [KeccakfPermAir.extraction.inter_4183, KeccakfPermAir.extraction.inter_4182, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4181 c row = (mc 2040 + mc 909 - mc 2431*mc 909 - 2*mc 2040*mc 909 + 2*mc 2040*mc 2431*mc 909) + 2 * KeccakfPermAir.extraction.inter_4179 c row := by
    simp only [KeccakfPermAir.extraction.inter_4181, KeccakfPermAir.extraction.inter_4180, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4179 c row = (mc 2041 + mc 910 - mc 2432*mc 910 - 2*mc 2041*mc 910 + 2*mc 2041*mc 2432*mc 910) + 2 * KeccakfPermAir.extraction.inter_4177 c row := by
    simp only [KeccakfPermAir.extraction.inter_4179, KeccakfPermAir.extraction.inter_4178, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4177 c row = (mc 2042 + mc 911 - mc 2433*mc 911 - 2*mc 2042*mc 911 + 2*mc 2042*mc 2433*mc 911) + 2 * KeccakfPermAir.extraction.inter_4175 c row := by
    simp only [KeccakfPermAir.extraction.inter_4177, KeccakfPermAir.extraction.inter_4176, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4175 c row = (mc 2043 + mc 912 - mc 2434*mc 912 - 2*mc 2043*mc 912 + 2*mc 2043*mc 2434*mc 912) := by
    simp only [KeccakfPermAir.extraction.inter_4175, KeccakfPermAir.extraction.inter_4174, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2925 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2925 c row) :
    ((mc 2044 + mc 913 - mc 2435*mc 913 - 2*mc 2044*mc 913 + 2*mc 2044*mc 2435*mc 913) + 2*(mc 2045 + mc 914 - mc 2436*mc 914 - 2*mc 2045*mc 914 + 2*mc 2045*mc 2436*mc 914) + 4*(mc 2046 + mc 915 - mc 2437*mc 915 - 2*mc 2046*mc 915 + 2*mc 2046*mc 2437*mc 915) + 8*(mc 2047 + mc 916 - mc 2438*mc 916 - 2*mc 2047*mc 916 + 2*mc 2047*mc 2438*mc 916) + 16*(mc 2048 + mc 917 - mc 2439*mc 917 - 2*mc 2048*mc 917 + 2*mc 2048*mc 2439*mc 917) + 32*(mc 2049 + mc 918 - mc 2440*mc 918 - 2*mc 2049*mc 918 + 2*mc 2049*mc 2440*mc 918) + 64*(mc 2050 + mc 919 - mc 2441*mc 919 - 2*mc 2050*mc 919 + 2*mc 2050*mc 2441*mc 919) + 128*(mc 2051 + mc 920 - mc 2442*mc 920 - 2*mc 2051*mc 920 + 2*mc 2051*mc 2442*mc 920) + 256*(mc 2052 + mc 921 - mc 2443*mc 921 - 2*mc 2052*mc 921 + 2*mc 2052*mc 2443*mc 921) + 512*(mc 2053 + mc 922 - mc 2444*mc 922 - 2*mc 2053*mc 922 + 2*mc 2053*mc 2444*mc 922) + 1024*(mc 2054 + mc 923 - mc 2445*mc 923 - 2*mc 2054*mc 923 + 2*mc 2054*mc 2445*mc 923) + 2048*(mc 2055 + mc 924 - mc 2446*mc 924 - 2*mc 2055*mc 924 + 2*mc 2055*mc 2446*mc 924) + 4096*(mc 2056 + mc 925 - mc 2447*mc 925 - 2*mc 2056*mc 925 + 2*mc 2056*mc 2447*mc 925) + 8192*(mc 2057 + mc 926 - mc 2448*mc 926 - 2*mc 2057*mc 926 + 2*mc 2057*mc 2448*mc 926) + 16384*(mc 2058 + mc 927 - mc 2449*mc 927 - 2*mc 2058*mc 927 + 2*mc 2058*mc 2449*mc 927) + 32768*(mc 2059 + mc 928 - mc 2450*mc 928 - 2*mc 2059*mc 928 + 2*mc 2059*mc 2450*mc 928)) - mc 2480 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2925, KeccakfPermAir.extraction.inter_4235, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4234 c row = (mc 2045 + mc 914 - mc 2436*mc 914 - 2*mc 2045*mc 914 + 2*mc 2045*mc 2436*mc 914) + 2 * KeccakfPermAir.extraction.inter_4232 c row := by
    simp only [KeccakfPermAir.extraction.inter_4234, KeccakfPermAir.extraction.inter_4233, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4232 c row = (mc 2046 + mc 915 - mc 2437*mc 915 - 2*mc 2046*mc 915 + 2*mc 2046*mc 2437*mc 915) + 2 * KeccakfPermAir.extraction.inter_4230 c row := by
    simp only [KeccakfPermAir.extraction.inter_4232, KeccakfPermAir.extraction.inter_4231, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4230 c row = (mc 2047 + mc 916 - mc 2438*mc 916 - 2*mc 2047*mc 916 + 2*mc 2047*mc 2438*mc 916) + 2 * KeccakfPermAir.extraction.inter_4228 c row := by
    simp only [KeccakfPermAir.extraction.inter_4230, KeccakfPermAir.extraction.inter_4229, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4228 c row = (mc 2048 + mc 917 - mc 2439*mc 917 - 2*mc 2048*mc 917 + 2*mc 2048*mc 2439*mc 917) + 2 * KeccakfPermAir.extraction.inter_4226 c row := by
    simp only [KeccakfPermAir.extraction.inter_4228, KeccakfPermAir.extraction.inter_4227, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4226 c row = (mc 2049 + mc 918 - mc 2440*mc 918 - 2*mc 2049*mc 918 + 2*mc 2049*mc 2440*mc 918) + 2 * KeccakfPermAir.extraction.inter_4224 c row := by
    simp only [KeccakfPermAir.extraction.inter_4226, KeccakfPermAir.extraction.inter_4225, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4224 c row = (mc 2050 + mc 919 - mc 2441*mc 919 - 2*mc 2050*mc 919 + 2*mc 2050*mc 2441*mc 919) + 2 * KeccakfPermAir.extraction.inter_4222 c row := by
    simp only [KeccakfPermAir.extraction.inter_4224, KeccakfPermAir.extraction.inter_4223, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4222 c row = (mc 2051 + mc 920 - mc 2442*mc 920 - 2*mc 2051*mc 920 + 2*mc 2051*mc 2442*mc 920) + 2 * KeccakfPermAir.extraction.inter_4220 c row := by
    simp only [KeccakfPermAir.extraction.inter_4222, KeccakfPermAir.extraction.inter_4221, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4220 c row = (mc 2052 + mc 921 - mc 2443*mc 921 - 2*mc 2052*mc 921 + 2*mc 2052*mc 2443*mc 921) + 2 * KeccakfPermAir.extraction.inter_4218 c row := by
    simp only [KeccakfPermAir.extraction.inter_4220, KeccakfPermAir.extraction.inter_4219, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4218 c row = (mc 2053 + mc 922 - mc 2444*mc 922 - 2*mc 2053*mc 922 + 2*mc 2053*mc 2444*mc 922) + 2 * KeccakfPermAir.extraction.inter_4216 c row := by
    simp only [KeccakfPermAir.extraction.inter_4218, KeccakfPermAir.extraction.inter_4217, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4216 c row = (mc 2054 + mc 923 - mc 2445*mc 923 - 2*mc 2054*mc 923 + 2*mc 2054*mc 2445*mc 923) + 2 * KeccakfPermAir.extraction.inter_4214 c row := by
    simp only [KeccakfPermAir.extraction.inter_4216, KeccakfPermAir.extraction.inter_4215, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4214 c row = (mc 2055 + mc 924 - mc 2446*mc 924 - 2*mc 2055*mc 924 + 2*mc 2055*mc 2446*mc 924) + 2 * KeccakfPermAir.extraction.inter_4212 c row := by
    simp only [KeccakfPermAir.extraction.inter_4214, KeccakfPermAir.extraction.inter_4213, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4212 c row = (mc 2056 + mc 925 - mc 2447*mc 925 - 2*mc 2056*mc 925 + 2*mc 2056*mc 2447*mc 925) + 2 * KeccakfPermAir.extraction.inter_4210 c row := by
    simp only [KeccakfPermAir.extraction.inter_4212, KeccakfPermAir.extraction.inter_4211, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4210 c row = (mc 2057 + mc 926 - mc 2448*mc 926 - 2*mc 2057*mc 926 + 2*mc 2057*mc 2448*mc 926) + 2 * KeccakfPermAir.extraction.inter_4208 c row := by
    simp only [KeccakfPermAir.extraction.inter_4210, KeccakfPermAir.extraction.inter_4209, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4208 c row = (mc 2058 + mc 927 - mc 2449*mc 927 - 2*mc 2058*mc 927 + 2*mc 2058*mc 2449*mc 927) + 2 * KeccakfPermAir.extraction.inter_4206 c row := by
    simp only [KeccakfPermAir.extraction.inter_4208, KeccakfPermAir.extraction.inter_4207, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4206 c row = (mc 2059 + mc 928 - mc 2450*mc 928 - 2*mc 2059*mc 928 + 2*mc 2059*mc 2450*mc 928) := by
    simp only [KeccakfPermAir.extraction.inter_4206, KeccakfPermAir.extraction.inter_4205, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2926 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2926 c row) :
    ((mc 2451 + mc 1269 - mc 865*mc 1269 - 2*mc 2451*mc 1269 + 2*mc 2451*mc 865*mc 1269) + 2*(mc 2452 + mc 1270 - mc 866*mc 1270 - 2*mc 2452*mc 1270 + 2*mc 2452*mc 866*mc 1270) + 4*(mc 2453 + mc 1271 - mc 867*mc 1271 - 2*mc 2453*mc 1271 + 2*mc 2453*mc 867*mc 1271) + 8*(mc 2454 + mc 1272 - mc 868*mc 1272 - 2*mc 2454*mc 1272 + 2*mc 2454*mc 868*mc 1272) + 16*(mc 2455 + mc 1273 - mc 869*mc 1273 - 2*mc 2455*mc 1273 + 2*mc 2455*mc 869*mc 1273) + 32*(mc 2456 + mc 1274 - mc 870*mc 1274 - 2*mc 2456*mc 1274 + 2*mc 2456*mc 870*mc 1274) + 64*(mc 2457 + mc 1275 - mc 871*mc 1275 - 2*mc 2457*mc 1275 + 2*mc 2457*mc 871*mc 1275) + 128*(mc 2458 + mc 1276 - mc 872*mc 1276 - 2*mc 2458*mc 1276 + 2*mc 2458*mc 872*mc 1276) + 256*(mc 2459 + mc 1277 - mc 873*mc 1277 - 2*mc 2459*mc 1277 + 2*mc 2459*mc 873*mc 1277) + 512*(mc 2460 + mc 1278 - mc 874*mc 1278 - 2*mc 2460*mc 1278 + 2*mc 2460*mc 874*mc 1278) + 1024*(mc 2461 + mc 1279 - mc 875*mc 1279 - 2*mc 2461*mc 1279 + 2*mc 2461*mc 875*mc 1279) + 2048*(mc 2462 + mc 1280 - mc 876*mc 1280 - 2*mc 2462*mc 1280 + 2*mc 2462*mc 876*mc 1280) + 4096*(mc 2463 + mc 1281 - mc 877*mc 1281 - 2*mc 2463*mc 1281 + 2*mc 2463*mc 877*mc 1281) + 8192*(mc 2464 + mc 1282 - mc 878*mc 1282 - 2*mc 2464*mc 1282 + 2*mc 2464*mc 878*mc 1282) + 16384*(mc 2401 + mc 1283 - mc 879*mc 1283 - 2*mc 2401*mc 1283 + 2*mc 2401*mc 879*mc 1283) + 32768*(mc 2402 + mc 1284 - mc 880*mc 1284 - 2*mc 2402*mc 1284 + 2*mc 2402*mc 880*mc 1284)) - mc 2481 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2926, KeccakfPermAir.extraction.inter_4266, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4265 c row = (mc 2452 + mc 1270 - mc 866*mc 1270 - 2*mc 2452*mc 1270 + 2*mc 2452*mc 866*mc 1270) + 2 * KeccakfPermAir.extraction.inter_4263 c row := by
    simp only [KeccakfPermAir.extraction.inter_4265, KeccakfPermAir.extraction.inter_4264, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4263 c row = (mc 2453 + mc 1271 - mc 867*mc 1271 - 2*mc 2453*mc 1271 + 2*mc 2453*mc 867*mc 1271) + 2 * KeccakfPermAir.extraction.inter_4261 c row := by
    simp only [KeccakfPermAir.extraction.inter_4263, KeccakfPermAir.extraction.inter_4262, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4261 c row = (mc 2454 + mc 1272 - mc 868*mc 1272 - 2*mc 2454*mc 1272 + 2*mc 2454*mc 868*mc 1272) + 2 * KeccakfPermAir.extraction.inter_4259 c row := by
    simp only [KeccakfPermAir.extraction.inter_4261, KeccakfPermAir.extraction.inter_4260, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4259 c row = (mc 2455 + mc 1273 - mc 869*mc 1273 - 2*mc 2455*mc 1273 + 2*mc 2455*mc 869*mc 1273) + 2 * KeccakfPermAir.extraction.inter_4257 c row := by
    simp only [KeccakfPermAir.extraction.inter_4259, KeccakfPermAir.extraction.inter_4258, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4257 c row = (mc 2456 + mc 1274 - mc 870*mc 1274 - 2*mc 2456*mc 1274 + 2*mc 2456*mc 870*mc 1274) + 2 * KeccakfPermAir.extraction.inter_4255 c row := by
    simp only [KeccakfPermAir.extraction.inter_4257, KeccakfPermAir.extraction.inter_4256, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4255 c row = (mc 2457 + mc 1275 - mc 871*mc 1275 - 2*mc 2457*mc 1275 + 2*mc 2457*mc 871*mc 1275) + 2 * KeccakfPermAir.extraction.inter_4253 c row := by
    simp only [KeccakfPermAir.extraction.inter_4255, KeccakfPermAir.extraction.inter_4254, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4253 c row = (mc 2458 + mc 1276 - mc 872*mc 1276 - 2*mc 2458*mc 1276 + 2*mc 2458*mc 872*mc 1276) + 2 * KeccakfPermAir.extraction.inter_4251 c row := by
    simp only [KeccakfPermAir.extraction.inter_4253, KeccakfPermAir.extraction.inter_4252, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4251 c row = (mc 2459 + mc 1277 - mc 873*mc 1277 - 2*mc 2459*mc 1277 + 2*mc 2459*mc 873*mc 1277) + 2 * KeccakfPermAir.extraction.inter_4249 c row := by
    simp only [KeccakfPermAir.extraction.inter_4251, KeccakfPermAir.extraction.inter_4250, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4249 c row = (mc 2460 + mc 1278 - mc 874*mc 1278 - 2*mc 2460*mc 1278 + 2*mc 2460*mc 874*mc 1278) + 2 * KeccakfPermAir.extraction.inter_4247 c row := by
    simp only [KeccakfPermAir.extraction.inter_4249, KeccakfPermAir.extraction.inter_4248, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4247 c row = (mc 2461 + mc 1279 - mc 875*mc 1279 - 2*mc 2461*mc 1279 + 2*mc 2461*mc 875*mc 1279) + 2 * KeccakfPermAir.extraction.inter_4245 c row := by
    simp only [KeccakfPermAir.extraction.inter_4247, KeccakfPermAir.extraction.inter_4246, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4245 c row = (mc 2462 + mc 1280 - mc 876*mc 1280 - 2*mc 2462*mc 1280 + 2*mc 2462*mc 876*mc 1280) + 2 * KeccakfPermAir.extraction.inter_4243 c row := by
    simp only [KeccakfPermAir.extraction.inter_4245, KeccakfPermAir.extraction.inter_4244, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4243 c row = (mc 2463 + mc 1281 - mc 877*mc 1281 - 2*mc 2463*mc 1281 + 2*mc 2463*mc 877*mc 1281) + 2 * KeccakfPermAir.extraction.inter_4241 c row := by
    simp only [KeccakfPermAir.extraction.inter_4243, KeccakfPermAir.extraction.inter_4242, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4241 c row = (mc 2464 + mc 1282 - mc 878*mc 1282 - 2*mc 2464*mc 1282 + 2*mc 2464*mc 878*mc 1282) + 2 * KeccakfPermAir.extraction.inter_4239 c row := by
    simp only [KeccakfPermAir.extraction.inter_4241, KeccakfPermAir.extraction.inter_4240, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4239 c row = (mc 2401 + mc 1283 - mc 879*mc 1283 - 2*mc 2401*mc 1283 + 2*mc 2401*mc 879*mc 1283) + 2 * KeccakfPermAir.extraction.inter_4237 c row := by
    simp only [KeccakfPermAir.extraction.inter_4239, KeccakfPermAir.extraction.inter_4238, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4237 c row = (mc 2402 + mc 1284 - mc 880*mc 1284 - 2*mc 2402*mc 1284 + 2*mc 2402*mc 880*mc 1284) := by
    simp only [KeccakfPermAir.extraction.inter_4237, KeccakfPermAir.extraction.inter_4236, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2927 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2927 c row) :
    ((mc 2403 + mc 1285 - mc 881*mc 1285 - 2*mc 2403*mc 1285 + 2*mc 2403*mc 881*mc 1285) + 2*(mc 2404 + mc 1286 - mc 882*mc 1286 - 2*mc 2404*mc 1286 + 2*mc 2404*mc 882*mc 1286) + 4*(mc 2405 + mc 1287 - mc 883*mc 1287 - 2*mc 2405*mc 1287 + 2*mc 2405*mc 883*mc 1287) + 8*(mc 2406 + mc 1288 - mc 884*mc 1288 - 2*mc 2406*mc 1288 + 2*mc 2406*mc 884*mc 1288) + 16*(mc 2407 + mc 1289 - mc 885*mc 1289 - 2*mc 2407*mc 1289 + 2*mc 2407*mc 885*mc 1289) + 32*(mc 2408 + mc 1290 - mc 886*mc 1290 - 2*mc 2408*mc 1290 + 2*mc 2408*mc 886*mc 1290) + 64*(mc 2409 + mc 1291 - mc 887*mc 1291 - 2*mc 2409*mc 1291 + 2*mc 2409*mc 887*mc 1291) + 128*(mc 2410 + mc 1292 - mc 888*mc 1292 - 2*mc 2410*mc 1292 + 2*mc 2410*mc 888*mc 1292) + 256*(mc 2411 + mc 1293 - mc 889*mc 1293 - 2*mc 2411*mc 1293 + 2*mc 2411*mc 889*mc 1293) + 512*(mc 2412 + mc 1294 - mc 890*mc 1294 - 2*mc 2412*mc 1294 + 2*mc 2412*mc 890*mc 1294) + 1024*(mc 2413 + mc 1295 - mc 891*mc 1295 - 2*mc 2413*mc 1295 + 2*mc 2413*mc 891*mc 1295) + 2048*(mc 2414 + mc 1296 - mc 892*mc 1296 - 2*mc 2414*mc 1296 + 2*mc 2414*mc 892*mc 1296) + 4096*(mc 2415 + mc 1297 - mc 893*mc 1297 - 2*mc 2415*mc 1297 + 2*mc 2415*mc 893*mc 1297) + 8192*(mc 2416 + mc 1298 - mc 894*mc 1298 - 2*mc 2416*mc 1298 + 2*mc 2416*mc 894*mc 1298) + 16384*(mc 2417 + mc 1299 - mc 895*mc 1299 - 2*mc 2417*mc 1299 + 2*mc 2417*mc 895*mc 1299) + 32768*(mc 2418 + mc 1300 - mc 896*mc 1300 - 2*mc 2418*mc 1300 + 2*mc 2418*mc 896*mc 1300)) - mc 2482 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2927, KeccakfPermAir.extraction.inter_4297, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4296 c row = (mc 2404 + mc 1286 - mc 882*mc 1286 - 2*mc 2404*mc 1286 + 2*mc 2404*mc 882*mc 1286) + 2 * KeccakfPermAir.extraction.inter_4294 c row := by
    simp only [KeccakfPermAir.extraction.inter_4296, KeccakfPermAir.extraction.inter_4295, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4294 c row = (mc 2405 + mc 1287 - mc 883*mc 1287 - 2*mc 2405*mc 1287 + 2*mc 2405*mc 883*mc 1287) + 2 * KeccakfPermAir.extraction.inter_4292 c row := by
    simp only [KeccakfPermAir.extraction.inter_4294, KeccakfPermAir.extraction.inter_4293, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4292 c row = (mc 2406 + mc 1288 - mc 884*mc 1288 - 2*mc 2406*mc 1288 + 2*mc 2406*mc 884*mc 1288) + 2 * KeccakfPermAir.extraction.inter_4290 c row := by
    simp only [KeccakfPermAir.extraction.inter_4292, KeccakfPermAir.extraction.inter_4291, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4290 c row = (mc 2407 + mc 1289 - mc 885*mc 1289 - 2*mc 2407*mc 1289 + 2*mc 2407*mc 885*mc 1289) + 2 * KeccakfPermAir.extraction.inter_4288 c row := by
    simp only [KeccakfPermAir.extraction.inter_4290, KeccakfPermAir.extraction.inter_4289, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4288 c row = (mc 2408 + mc 1290 - mc 886*mc 1290 - 2*mc 2408*mc 1290 + 2*mc 2408*mc 886*mc 1290) + 2 * KeccakfPermAir.extraction.inter_4286 c row := by
    simp only [KeccakfPermAir.extraction.inter_4288, KeccakfPermAir.extraction.inter_4287, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4286 c row = (mc 2409 + mc 1291 - mc 887*mc 1291 - 2*mc 2409*mc 1291 + 2*mc 2409*mc 887*mc 1291) + 2 * KeccakfPermAir.extraction.inter_4284 c row := by
    simp only [KeccakfPermAir.extraction.inter_4286, KeccakfPermAir.extraction.inter_4285, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4284 c row = (mc 2410 + mc 1292 - mc 888*mc 1292 - 2*mc 2410*mc 1292 + 2*mc 2410*mc 888*mc 1292) + 2 * KeccakfPermAir.extraction.inter_4282 c row := by
    simp only [KeccakfPermAir.extraction.inter_4284, KeccakfPermAir.extraction.inter_4283, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4282 c row = (mc 2411 + mc 1293 - mc 889*mc 1293 - 2*mc 2411*mc 1293 + 2*mc 2411*mc 889*mc 1293) + 2 * KeccakfPermAir.extraction.inter_4280 c row := by
    simp only [KeccakfPermAir.extraction.inter_4282, KeccakfPermAir.extraction.inter_4281, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4280 c row = (mc 2412 + mc 1294 - mc 890*mc 1294 - 2*mc 2412*mc 1294 + 2*mc 2412*mc 890*mc 1294) + 2 * KeccakfPermAir.extraction.inter_4278 c row := by
    simp only [KeccakfPermAir.extraction.inter_4280, KeccakfPermAir.extraction.inter_4279, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4278 c row = (mc 2413 + mc 1295 - mc 891*mc 1295 - 2*mc 2413*mc 1295 + 2*mc 2413*mc 891*mc 1295) + 2 * KeccakfPermAir.extraction.inter_4276 c row := by
    simp only [KeccakfPermAir.extraction.inter_4278, KeccakfPermAir.extraction.inter_4277, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4276 c row = (mc 2414 + mc 1296 - mc 892*mc 1296 - 2*mc 2414*mc 1296 + 2*mc 2414*mc 892*mc 1296) + 2 * KeccakfPermAir.extraction.inter_4274 c row := by
    simp only [KeccakfPermAir.extraction.inter_4276, KeccakfPermAir.extraction.inter_4275, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4274 c row = (mc 2415 + mc 1297 - mc 893*mc 1297 - 2*mc 2415*mc 1297 + 2*mc 2415*mc 893*mc 1297) + 2 * KeccakfPermAir.extraction.inter_4272 c row := by
    simp only [KeccakfPermAir.extraction.inter_4274, KeccakfPermAir.extraction.inter_4273, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4272 c row = (mc 2416 + mc 1298 - mc 894*mc 1298 - 2*mc 2416*mc 1298 + 2*mc 2416*mc 894*mc 1298) + 2 * KeccakfPermAir.extraction.inter_4270 c row := by
    simp only [KeccakfPermAir.extraction.inter_4272, KeccakfPermAir.extraction.inter_4271, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4270 c row = (mc 2417 + mc 1299 - mc 895*mc 1299 - 2*mc 2417*mc 1299 + 2*mc 2417*mc 895*mc 1299) + 2 * KeccakfPermAir.extraction.inter_4268 c row := by
    simp only [KeccakfPermAir.extraction.inter_4270, KeccakfPermAir.extraction.inter_4269, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4268 c row = (mc 2418 + mc 1300 - mc 896*mc 1300 - 2*mc 2418*mc 1300 + 2*mc 2418*mc 896*mc 1300) := by
    simp only [KeccakfPermAir.extraction.inter_4268, KeccakfPermAir.extraction.inter_4267, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2928 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2928 c row) :
    ((mc 2419 + mc 1301 - mc 897*mc 1301 - 2*mc 2419*mc 1301 + 2*mc 2419*mc 897*mc 1301) + 2*(mc 2420 + mc 1302 - mc 898*mc 1302 - 2*mc 2420*mc 1302 + 2*mc 2420*mc 898*mc 1302) + 4*(mc 2421 + mc 1303 - mc 899*mc 1303 - 2*mc 2421*mc 1303 + 2*mc 2421*mc 899*mc 1303) + 8*(mc 2422 + mc 1304 - mc 900*mc 1304 - 2*mc 2422*mc 1304 + 2*mc 2422*mc 900*mc 1304) + 16*(mc 2423 + mc 1305 - mc 901*mc 1305 - 2*mc 2423*mc 1305 + 2*mc 2423*mc 901*mc 1305) + 32*(mc 2424 + mc 1306 - mc 902*mc 1306 - 2*mc 2424*mc 1306 + 2*mc 2424*mc 902*mc 1306) + 64*(mc 2425 + mc 1307 - mc 903*mc 1307 - 2*mc 2425*mc 1307 + 2*mc 2425*mc 903*mc 1307) + 128*(mc 2426 + mc 1308 - mc 904*mc 1308 - 2*mc 2426*mc 1308 + 2*mc 2426*mc 904*mc 1308) + 256*(mc 2427 + mc 1309 - mc 905*mc 1309 - 2*mc 2427*mc 1309 + 2*mc 2427*mc 905*mc 1309) + 512*(mc 2428 + mc 1310 - mc 906*mc 1310 - 2*mc 2428*mc 1310 + 2*mc 2428*mc 906*mc 1310) + 1024*(mc 2429 + mc 1311 - mc 907*mc 1311 - 2*mc 2429*mc 1311 + 2*mc 2429*mc 907*mc 1311) + 2048*(mc 2430 + mc 1312 - mc 908*mc 1312 - 2*mc 2430*mc 1312 + 2*mc 2430*mc 908*mc 1312) + 4096*(mc 2431 + mc 1249 - mc 909*mc 1249 - 2*mc 2431*mc 1249 + 2*mc 2431*mc 909*mc 1249) + 8192*(mc 2432 + mc 1250 - mc 910*mc 1250 - 2*mc 2432*mc 1250 + 2*mc 2432*mc 910*mc 1250) + 16384*(mc 2433 + mc 1251 - mc 911*mc 1251 - 2*mc 2433*mc 1251 + 2*mc 2433*mc 911*mc 1251) + 32768*(mc 2434 + mc 1252 - mc 912*mc 1252 - 2*mc 2434*mc 1252 + 2*mc 2434*mc 912*mc 1252)) - mc 2483 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2928, KeccakfPermAir.extraction.inter_4328, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4327 c row = (mc 2420 + mc 1302 - mc 898*mc 1302 - 2*mc 2420*mc 1302 + 2*mc 2420*mc 898*mc 1302) + 2 * KeccakfPermAir.extraction.inter_4325 c row := by
    simp only [KeccakfPermAir.extraction.inter_4327, KeccakfPermAir.extraction.inter_4326, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4325 c row = (mc 2421 + mc 1303 - mc 899*mc 1303 - 2*mc 2421*mc 1303 + 2*mc 2421*mc 899*mc 1303) + 2 * KeccakfPermAir.extraction.inter_4323 c row := by
    simp only [KeccakfPermAir.extraction.inter_4325, KeccakfPermAir.extraction.inter_4324, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4323 c row = (mc 2422 + mc 1304 - mc 900*mc 1304 - 2*mc 2422*mc 1304 + 2*mc 2422*mc 900*mc 1304) + 2 * KeccakfPermAir.extraction.inter_4321 c row := by
    simp only [KeccakfPermAir.extraction.inter_4323, KeccakfPermAir.extraction.inter_4322, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4321 c row = (mc 2423 + mc 1305 - mc 901*mc 1305 - 2*mc 2423*mc 1305 + 2*mc 2423*mc 901*mc 1305) + 2 * KeccakfPermAir.extraction.inter_4319 c row := by
    simp only [KeccakfPermAir.extraction.inter_4321, KeccakfPermAir.extraction.inter_4320, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4319 c row = (mc 2424 + mc 1306 - mc 902*mc 1306 - 2*mc 2424*mc 1306 + 2*mc 2424*mc 902*mc 1306) + 2 * KeccakfPermAir.extraction.inter_4317 c row := by
    simp only [KeccakfPermAir.extraction.inter_4319, KeccakfPermAir.extraction.inter_4318, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4317 c row = (mc 2425 + mc 1307 - mc 903*mc 1307 - 2*mc 2425*mc 1307 + 2*mc 2425*mc 903*mc 1307) + 2 * KeccakfPermAir.extraction.inter_4315 c row := by
    simp only [KeccakfPermAir.extraction.inter_4317, KeccakfPermAir.extraction.inter_4316, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4315 c row = (mc 2426 + mc 1308 - mc 904*mc 1308 - 2*mc 2426*mc 1308 + 2*mc 2426*mc 904*mc 1308) + 2 * KeccakfPermAir.extraction.inter_4313 c row := by
    simp only [KeccakfPermAir.extraction.inter_4315, KeccakfPermAir.extraction.inter_4314, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4313 c row = (mc 2427 + mc 1309 - mc 905*mc 1309 - 2*mc 2427*mc 1309 + 2*mc 2427*mc 905*mc 1309) + 2 * KeccakfPermAir.extraction.inter_4311 c row := by
    simp only [KeccakfPermAir.extraction.inter_4313, KeccakfPermAir.extraction.inter_4312, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4311 c row = (mc 2428 + mc 1310 - mc 906*mc 1310 - 2*mc 2428*mc 1310 + 2*mc 2428*mc 906*mc 1310) + 2 * KeccakfPermAir.extraction.inter_4309 c row := by
    simp only [KeccakfPermAir.extraction.inter_4311, KeccakfPermAir.extraction.inter_4310, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4309 c row = (mc 2429 + mc 1311 - mc 907*mc 1311 - 2*mc 2429*mc 1311 + 2*mc 2429*mc 907*mc 1311) + 2 * KeccakfPermAir.extraction.inter_4307 c row := by
    simp only [KeccakfPermAir.extraction.inter_4309, KeccakfPermAir.extraction.inter_4308, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4307 c row = (mc 2430 + mc 1312 - mc 908*mc 1312 - 2*mc 2430*mc 1312 + 2*mc 2430*mc 908*mc 1312) + 2 * KeccakfPermAir.extraction.inter_4305 c row := by
    simp only [KeccakfPermAir.extraction.inter_4307, KeccakfPermAir.extraction.inter_4306, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4305 c row = (mc 2431 + mc 1249 - mc 909*mc 1249 - 2*mc 2431*mc 1249 + 2*mc 2431*mc 909*mc 1249) + 2 * KeccakfPermAir.extraction.inter_4303 c row := by
    simp only [KeccakfPermAir.extraction.inter_4305, KeccakfPermAir.extraction.inter_4304, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4303 c row = (mc 2432 + mc 1250 - mc 910*mc 1250 - 2*mc 2432*mc 1250 + 2*mc 2432*mc 910*mc 1250) + 2 * KeccakfPermAir.extraction.inter_4301 c row := by
    simp only [KeccakfPermAir.extraction.inter_4303, KeccakfPermAir.extraction.inter_4302, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4301 c row = (mc 2433 + mc 1251 - mc 911*mc 1251 - 2*mc 2433*mc 1251 + 2*mc 2433*mc 911*mc 1251) + 2 * KeccakfPermAir.extraction.inter_4299 c row := by
    simp only [KeccakfPermAir.extraction.inter_4301, KeccakfPermAir.extraction.inter_4300, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4299 c row = (mc 2434 + mc 1252 - mc 912*mc 1252 - 2*mc 2434*mc 1252 + 2*mc 2434*mc 912*mc 1252) := by
    simp only [KeccakfPermAir.extraction.inter_4299, KeccakfPermAir.extraction.inter_4298, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2929 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2929 c row) :
    ((mc 2435 + mc 1253 - mc 913*mc 1253 - 2*mc 2435*mc 1253 + 2*mc 2435*mc 913*mc 1253) + 2*(mc 2436 + mc 1254 - mc 914*mc 1254 - 2*mc 2436*mc 1254 + 2*mc 2436*mc 914*mc 1254) + 4*(mc 2437 + mc 1255 - mc 915*mc 1255 - 2*mc 2437*mc 1255 + 2*mc 2437*mc 915*mc 1255) + 8*(mc 2438 + mc 1256 - mc 916*mc 1256 - 2*mc 2438*mc 1256 + 2*mc 2438*mc 916*mc 1256) + 16*(mc 2439 + mc 1257 - mc 917*mc 1257 - 2*mc 2439*mc 1257 + 2*mc 2439*mc 917*mc 1257) + 32*(mc 2440 + mc 1258 - mc 918*mc 1258 - 2*mc 2440*mc 1258 + 2*mc 2440*mc 918*mc 1258) + 64*(mc 2441 + mc 1259 - mc 919*mc 1259 - 2*mc 2441*mc 1259 + 2*mc 2441*mc 919*mc 1259) + 128*(mc 2442 + mc 1260 - mc 920*mc 1260 - 2*mc 2442*mc 1260 + 2*mc 2442*mc 920*mc 1260) + 256*(mc 2443 + mc 1261 - mc 921*mc 1261 - 2*mc 2443*mc 1261 + 2*mc 2443*mc 921*mc 1261) + 512*(mc 2444 + mc 1262 - mc 922*mc 1262 - 2*mc 2444*mc 1262 + 2*mc 2444*mc 922*mc 1262) + 1024*(mc 2445 + mc 1263 - mc 923*mc 1263 - 2*mc 2445*mc 1263 + 2*mc 2445*mc 923*mc 1263) + 2048*(mc 2446 + mc 1264 - mc 924*mc 1264 - 2*mc 2446*mc 1264 + 2*mc 2446*mc 924*mc 1264) + 4096*(mc 2447 + mc 1265 - mc 925*mc 1265 - 2*mc 2447*mc 1265 + 2*mc 2447*mc 925*mc 1265) + 8192*(mc 2448 + mc 1266 - mc 926*mc 1266 - 2*mc 2448*mc 1266 + 2*mc 2448*mc 926*mc 1266) + 16384*(mc 2449 + mc 1267 - mc 927*mc 1267 - 2*mc 2449*mc 1267 + 2*mc 2449*mc 927*mc 1267) + 32768*(mc 2450 + mc 1268 - mc 928*mc 1268 - 2*mc 2450*mc 1268 + 2*mc 2450*mc 928*mc 1268)) - mc 2484 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2929, KeccakfPermAir.extraction.inter_4359, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4358 c row = (mc 2436 + mc 1254 - mc 914*mc 1254 - 2*mc 2436*mc 1254 + 2*mc 2436*mc 914*mc 1254) + 2 * KeccakfPermAir.extraction.inter_4356 c row := by
    simp only [KeccakfPermAir.extraction.inter_4358, KeccakfPermAir.extraction.inter_4357, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4356 c row = (mc 2437 + mc 1255 - mc 915*mc 1255 - 2*mc 2437*mc 1255 + 2*mc 2437*mc 915*mc 1255) + 2 * KeccakfPermAir.extraction.inter_4354 c row := by
    simp only [KeccakfPermAir.extraction.inter_4356, KeccakfPermAir.extraction.inter_4355, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4354 c row = (mc 2438 + mc 1256 - mc 916*mc 1256 - 2*mc 2438*mc 1256 + 2*mc 2438*mc 916*mc 1256) + 2 * KeccakfPermAir.extraction.inter_4352 c row := by
    simp only [KeccakfPermAir.extraction.inter_4354, KeccakfPermAir.extraction.inter_4353, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4352 c row = (mc 2439 + mc 1257 - mc 917*mc 1257 - 2*mc 2439*mc 1257 + 2*mc 2439*mc 917*mc 1257) + 2 * KeccakfPermAir.extraction.inter_4350 c row := by
    simp only [KeccakfPermAir.extraction.inter_4352, KeccakfPermAir.extraction.inter_4351, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4350 c row = (mc 2440 + mc 1258 - mc 918*mc 1258 - 2*mc 2440*mc 1258 + 2*mc 2440*mc 918*mc 1258) + 2 * KeccakfPermAir.extraction.inter_4348 c row := by
    simp only [KeccakfPermAir.extraction.inter_4350, KeccakfPermAir.extraction.inter_4349, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4348 c row = (mc 2441 + mc 1259 - mc 919*mc 1259 - 2*mc 2441*mc 1259 + 2*mc 2441*mc 919*mc 1259) + 2 * KeccakfPermAir.extraction.inter_4346 c row := by
    simp only [KeccakfPermAir.extraction.inter_4348, KeccakfPermAir.extraction.inter_4347, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4346 c row = (mc 2442 + mc 1260 - mc 920*mc 1260 - 2*mc 2442*mc 1260 + 2*mc 2442*mc 920*mc 1260) + 2 * KeccakfPermAir.extraction.inter_4344 c row := by
    simp only [KeccakfPermAir.extraction.inter_4346, KeccakfPermAir.extraction.inter_4345, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4344 c row = (mc 2443 + mc 1261 - mc 921*mc 1261 - 2*mc 2443*mc 1261 + 2*mc 2443*mc 921*mc 1261) + 2 * KeccakfPermAir.extraction.inter_4342 c row := by
    simp only [KeccakfPermAir.extraction.inter_4344, KeccakfPermAir.extraction.inter_4343, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4342 c row = (mc 2444 + mc 1262 - mc 922*mc 1262 - 2*mc 2444*mc 1262 + 2*mc 2444*mc 922*mc 1262) + 2 * KeccakfPermAir.extraction.inter_4340 c row := by
    simp only [KeccakfPermAir.extraction.inter_4342, KeccakfPermAir.extraction.inter_4341, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4340 c row = (mc 2445 + mc 1263 - mc 923*mc 1263 - 2*mc 2445*mc 1263 + 2*mc 2445*mc 923*mc 1263) + 2 * KeccakfPermAir.extraction.inter_4338 c row := by
    simp only [KeccakfPermAir.extraction.inter_4340, KeccakfPermAir.extraction.inter_4339, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4338 c row = (mc 2446 + mc 1264 - mc 924*mc 1264 - 2*mc 2446*mc 1264 + 2*mc 2446*mc 924*mc 1264) + 2 * KeccakfPermAir.extraction.inter_4336 c row := by
    simp only [KeccakfPermAir.extraction.inter_4338, KeccakfPermAir.extraction.inter_4337, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4336 c row = (mc 2447 + mc 1265 - mc 925*mc 1265 - 2*mc 2447*mc 1265 + 2*mc 2447*mc 925*mc 1265) + 2 * KeccakfPermAir.extraction.inter_4334 c row := by
    simp only [KeccakfPermAir.extraction.inter_4336, KeccakfPermAir.extraction.inter_4335, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4334 c row = (mc 2448 + mc 1266 - mc 926*mc 1266 - 2*mc 2448*mc 1266 + 2*mc 2448*mc 926*mc 1266) + 2 * KeccakfPermAir.extraction.inter_4332 c row := by
    simp only [KeccakfPermAir.extraction.inter_4334, KeccakfPermAir.extraction.inter_4333, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4332 c row = (mc 2449 + mc 1267 - mc 927*mc 1267 - 2*mc 2449*mc 1267 + 2*mc 2449*mc 927*mc 1267) + 2 * KeccakfPermAir.extraction.inter_4330 c row := by
    simp only [KeccakfPermAir.extraction.inter_4332, KeccakfPermAir.extraction.inter_4331, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4330 c row = (mc 2450 + mc 1268 - mc 928*mc 1268 - 2*mc 2450*mc 1268 + 2*mc 2450*mc 928*mc 1268) := by
    simp only [KeccakfPermAir.extraction.inter_4330, KeccakfPermAir.extraction.inter_4329, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2930 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2930 c row) :
    ((mc 1093 + mc 1566 - mc 1485*mc 1566 - 2*mc 1093*mc 1566 + 2*mc 1093*mc 1485*mc 1566) + 2*(mc 1094 + mc 1567 - mc 1486*mc 1567 - 2*mc 1094*mc 1567 + 2*mc 1094*mc 1486*mc 1567) + 4*(mc 1095 + mc 1568 - mc 1487*mc 1568 - 2*mc 1095*mc 1568 + 2*mc 1095*mc 1487*mc 1568) + 8*(mc 1096 + mc 1505 - mc 1488*mc 1505 - 2*mc 1096*mc 1505 + 2*mc 1096*mc 1488*mc 1505) + 16*(mc 1097 + mc 1506 - mc 1489*mc 1506 - 2*mc 1097*mc 1506 + 2*mc 1097*mc 1489*mc 1506) + 32*(mc 1098 + mc 1507 - mc 1490*mc 1507 - 2*mc 1098*mc 1507 + 2*mc 1098*mc 1490*mc 1507) + 64*(mc 1099 + mc 1508 - mc 1491*mc 1508 - 2*mc 1099*mc 1508 + 2*mc 1099*mc 1491*mc 1508) + 128*(mc 1100 + mc 1509 - mc 1492*mc 1509 - 2*mc 1100*mc 1509 + 2*mc 1100*mc 1492*mc 1509) + 256*(mc 1101 + mc 1510 - mc 1493*mc 1510 - 2*mc 1101*mc 1510 + 2*mc 1101*mc 1493*mc 1510) + 512*(mc 1102 + mc 1511 - mc 1494*mc 1511 - 2*mc 1102*mc 1511 + 2*mc 1102*mc 1494*mc 1511) + 1024*(mc 1103 + mc 1512 - mc 1495*mc 1512 - 2*mc 1103*mc 1512 + 2*mc 1103*mc 1495*mc 1512) + 2048*(mc 1104 + mc 1513 - mc 1496*mc 1513 - 2*mc 1104*mc 1513 + 2*mc 1104*mc 1496*mc 1513) + 4096*(mc 1105 + mc 1514 - mc 1497*mc 1514 - 2*mc 1105*mc 1514 + 2*mc 1105*mc 1497*mc 1514) + 8192*(mc 1106 + mc 1515 - mc 1498*mc 1515 - 2*mc 1106*mc 1515 + 2*mc 1106*mc 1498*mc 1515) + 16384*(mc 1107 + mc 1516 - mc 1499*mc 1516 - 2*mc 1107*mc 1516 + 2*mc 1107*mc 1499*mc 1516) + 32768*(mc 1108 + mc 1517 - mc 1500*mc 1517 - 2*mc 1108*mc 1517 + 2*mc 1108*mc 1500*mc 1517)) - mc 2485 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2930, KeccakfPermAir.extraction.inter_4390, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4389 c row = (mc 1094 + mc 1567 - mc 1486*mc 1567 - 2*mc 1094*mc 1567 + 2*mc 1094*mc 1486*mc 1567) + 2 * KeccakfPermAir.extraction.inter_4387 c row := by
    simp only [KeccakfPermAir.extraction.inter_4389, KeccakfPermAir.extraction.inter_4388, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4387 c row = (mc 1095 + mc 1568 - mc 1487*mc 1568 - 2*mc 1095*mc 1568 + 2*mc 1095*mc 1487*mc 1568) + 2 * KeccakfPermAir.extraction.inter_4385 c row := by
    simp only [KeccakfPermAir.extraction.inter_4387, KeccakfPermAir.extraction.inter_4386, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4385 c row = (mc 1096 + mc 1505 - mc 1488*mc 1505 - 2*mc 1096*mc 1505 + 2*mc 1096*mc 1488*mc 1505) + 2 * KeccakfPermAir.extraction.inter_4383 c row := by
    simp only [KeccakfPermAir.extraction.inter_4385, KeccakfPermAir.extraction.inter_4384, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4383 c row = (mc 1097 + mc 1506 - mc 1489*mc 1506 - 2*mc 1097*mc 1506 + 2*mc 1097*mc 1489*mc 1506) + 2 * KeccakfPermAir.extraction.inter_4381 c row := by
    simp only [KeccakfPermAir.extraction.inter_4383, KeccakfPermAir.extraction.inter_4382, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4381 c row = (mc 1098 + mc 1507 - mc 1490*mc 1507 - 2*mc 1098*mc 1507 + 2*mc 1098*mc 1490*mc 1507) + 2 * KeccakfPermAir.extraction.inter_4379 c row := by
    simp only [KeccakfPermAir.extraction.inter_4381, KeccakfPermAir.extraction.inter_4380, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4379 c row = (mc 1099 + mc 1508 - mc 1491*mc 1508 - 2*mc 1099*mc 1508 + 2*mc 1099*mc 1491*mc 1508) + 2 * KeccakfPermAir.extraction.inter_4377 c row := by
    simp only [KeccakfPermAir.extraction.inter_4379, KeccakfPermAir.extraction.inter_4378, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4377 c row = (mc 1100 + mc 1509 - mc 1492*mc 1509 - 2*mc 1100*mc 1509 + 2*mc 1100*mc 1492*mc 1509) + 2 * KeccakfPermAir.extraction.inter_4375 c row := by
    simp only [KeccakfPermAir.extraction.inter_4377, KeccakfPermAir.extraction.inter_4376, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4375 c row = (mc 1101 + mc 1510 - mc 1493*mc 1510 - 2*mc 1101*mc 1510 + 2*mc 1101*mc 1493*mc 1510) + 2 * KeccakfPermAir.extraction.inter_4373 c row := by
    simp only [KeccakfPermAir.extraction.inter_4375, KeccakfPermAir.extraction.inter_4374, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4373 c row = (mc 1102 + mc 1511 - mc 1494*mc 1511 - 2*mc 1102*mc 1511 + 2*mc 1102*mc 1494*mc 1511) + 2 * KeccakfPermAir.extraction.inter_4371 c row := by
    simp only [KeccakfPermAir.extraction.inter_4373, KeccakfPermAir.extraction.inter_4372, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4371 c row = (mc 1103 + mc 1512 - mc 1495*mc 1512 - 2*mc 1103*mc 1512 + 2*mc 1103*mc 1495*mc 1512) + 2 * KeccakfPermAir.extraction.inter_4369 c row := by
    simp only [KeccakfPermAir.extraction.inter_4371, KeccakfPermAir.extraction.inter_4370, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4369 c row = (mc 1104 + mc 1513 - mc 1496*mc 1513 - 2*mc 1104*mc 1513 + 2*mc 1104*mc 1496*mc 1513) + 2 * KeccakfPermAir.extraction.inter_4367 c row := by
    simp only [KeccakfPermAir.extraction.inter_4369, KeccakfPermAir.extraction.inter_4368, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4367 c row = (mc 1105 + mc 1514 - mc 1497*mc 1514 - 2*mc 1105*mc 1514 + 2*mc 1105*mc 1497*mc 1514) + 2 * KeccakfPermAir.extraction.inter_4365 c row := by
    simp only [KeccakfPermAir.extraction.inter_4367, KeccakfPermAir.extraction.inter_4366, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4365 c row = (mc 1106 + mc 1515 - mc 1498*mc 1515 - 2*mc 1106*mc 1515 + 2*mc 1106*mc 1498*mc 1515) + 2 * KeccakfPermAir.extraction.inter_4363 c row := by
    simp only [KeccakfPermAir.extraction.inter_4365, KeccakfPermAir.extraction.inter_4364, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4363 c row = (mc 1107 + mc 1516 - mc 1499*mc 1516 - 2*mc 1107*mc 1516 + 2*mc 1107*mc 1499*mc 1516) + 2 * KeccakfPermAir.extraction.inter_4361 c row := by
    simp only [KeccakfPermAir.extraction.inter_4363, KeccakfPermAir.extraction.inter_4362, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4361 c row = (mc 1108 + mc 1517 - mc 1500*mc 1517 - 2*mc 1108*mc 1517 + 2*mc 1108*mc 1500*mc 1517) := by
    simp only [KeccakfPermAir.extraction.inter_4361, KeccakfPermAir.extraction.inter_4360, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2931 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2931 c row) :
    ((mc 1109 + mc 1518 - mc 1501*mc 1518 - 2*mc 1109*mc 1518 + 2*mc 1109*mc 1501*mc 1518) + 2*(mc 1110 + mc 1519 - mc 1502*mc 1519 - 2*mc 1110*mc 1519 + 2*mc 1110*mc 1502*mc 1519) + 4*(mc 1111 + mc 1520 - mc 1503*mc 1520 - 2*mc 1111*mc 1520 + 2*mc 1111*mc 1503*mc 1520) + 8*(mc 1112 + mc 1521 - mc 1504*mc 1521 - 2*mc 1112*mc 1521 + 2*mc 1112*mc 1504*mc 1521) + 16*(mc 1113 + mc 1522 - mc 1441*mc 1522 - 2*mc 1113*mc 1522 + 2*mc 1113*mc 1441*mc 1522) + 32*(mc 1114 + mc 1523 - mc 1442*mc 1523 - 2*mc 1114*mc 1523 + 2*mc 1114*mc 1442*mc 1523) + 64*(mc 1115 + mc 1524 - mc 1443*mc 1524 - 2*mc 1115*mc 1524 + 2*mc 1115*mc 1443*mc 1524) + 128*(mc 1116 + mc 1525 - mc 1444*mc 1525 - 2*mc 1116*mc 1525 + 2*mc 1116*mc 1444*mc 1525) + 256*(mc 1117 + mc 1526 - mc 1445*mc 1526 - 2*mc 1117*mc 1526 + 2*mc 1117*mc 1445*mc 1526) + 512*(mc 1118 + mc 1527 - mc 1446*mc 1527 - 2*mc 1118*mc 1527 + 2*mc 1118*mc 1446*mc 1527) + 1024*(mc 1119 + mc 1528 - mc 1447*mc 1528 - 2*mc 1119*mc 1528 + 2*mc 1119*mc 1447*mc 1528) + 2048*(mc 1120 + mc 1529 - mc 1448*mc 1529 - 2*mc 1120*mc 1529 + 2*mc 1120*mc 1448*mc 1529) + 4096*(mc 1057 + mc 1530 - mc 1449*mc 1530 - 2*mc 1057*mc 1530 + 2*mc 1057*mc 1449*mc 1530) + 8192*(mc 1058 + mc 1531 - mc 1450*mc 1531 - 2*mc 1058*mc 1531 + 2*mc 1058*mc 1450*mc 1531) + 16384*(mc 1059 + mc 1532 - mc 1451*mc 1532 - 2*mc 1059*mc 1532 + 2*mc 1059*mc 1451*mc 1532) + 32768*(mc 1060 + mc 1533 - mc 1452*mc 1533 - 2*mc 1060*mc 1533 + 2*mc 1060*mc 1452*mc 1533)) - mc 2486 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2931, KeccakfPermAir.extraction.inter_4421, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4420 c row = (mc 1110 + mc 1519 - mc 1502*mc 1519 - 2*mc 1110*mc 1519 + 2*mc 1110*mc 1502*mc 1519) + 2 * KeccakfPermAir.extraction.inter_4418 c row := by
    simp only [KeccakfPermAir.extraction.inter_4420, KeccakfPermAir.extraction.inter_4419, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4418 c row = (mc 1111 + mc 1520 - mc 1503*mc 1520 - 2*mc 1111*mc 1520 + 2*mc 1111*mc 1503*mc 1520) + 2 * KeccakfPermAir.extraction.inter_4416 c row := by
    simp only [KeccakfPermAir.extraction.inter_4418, KeccakfPermAir.extraction.inter_4417, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4416 c row = (mc 1112 + mc 1521 - mc 1504*mc 1521 - 2*mc 1112*mc 1521 + 2*mc 1112*mc 1504*mc 1521) + 2 * KeccakfPermAir.extraction.inter_4414 c row := by
    simp only [KeccakfPermAir.extraction.inter_4416, KeccakfPermAir.extraction.inter_4415, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4414 c row = (mc 1113 + mc 1522 - mc 1441*mc 1522 - 2*mc 1113*mc 1522 + 2*mc 1113*mc 1441*mc 1522) + 2 * KeccakfPermAir.extraction.inter_4412 c row := by
    simp only [KeccakfPermAir.extraction.inter_4414, KeccakfPermAir.extraction.inter_4413, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4412 c row = (mc 1114 + mc 1523 - mc 1442*mc 1523 - 2*mc 1114*mc 1523 + 2*mc 1114*mc 1442*mc 1523) + 2 * KeccakfPermAir.extraction.inter_4410 c row := by
    simp only [KeccakfPermAir.extraction.inter_4412, KeccakfPermAir.extraction.inter_4411, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4410 c row = (mc 1115 + mc 1524 - mc 1443*mc 1524 - 2*mc 1115*mc 1524 + 2*mc 1115*mc 1443*mc 1524) + 2 * KeccakfPermAir.extraction.inter_4408 c row := by
    simp only [KeccakfPermAir.extraction.inter_4410, KeccakfPermAir.extraction.inter_4409, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4408 c row = (mc 1116 + mc 1525 - mc 1444*mc 1525 - 2*mc 1116*mc 1525 + 2*mc 1116*mc 1444*mc 1525) + 2 * KeccakfPermAir.extraction.inter_4406 c row := by
    simp only [KeccakfPermAir.extraction.inter_4408, KeccakfPermAir.extraction.inter_4407, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4406 c row = (mc 1117 + mc 1526 - mc 1445*mc 1526 - 2*mc 1117*mc 1526 + 2*mc 1117*mc 1445*mc 1526) + 2 * KeccakfPermAir.extraction.inter_4404 c row := by
    simp only [KeccakfPermAir.extraction.inter_4406, KeccakfPermAir.extraction.inter_4405, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4404 c row = (mc 1118 + mc 1527 - mc 1446*mc 1527 - 2*mc 1118*mc 1527 + 2*mc 1118*mc 1446*mc 1527) + 2 * KeccakfPermAir.extraction.inter_4402 c row := by
    simp only [KeccakfPermAir.extraction.inter_4404, KeccakfPermAir.extraction.inter_4403, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4402 c row = (mc 1119 + mc 1528 - mc 1447*mc 1528 - 2*mc 1119*mc 1528 + 2*mc 1119*mc 1447*mc 1528) + 2 * KeccakfPermAir.extraction.inter_4400 c row := by
    simp only [KeccakfPermAir.extraction.inter_4402, KeccakfPermAir.extraction.inter_4401, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4400 c row = (mc 1120 + mc 1529 - mc 1448*mc 1529 - 2*mc 1120*mc 1529 + 2*mc 1120*mc 1448*mc 1529) + 2 * KeccakfPermAir.extraction.inter_4398 c row := by
    simp only [KeccakfPermAir.extraction.inter_4400, KeccakfPermAir.extraction.inter_4399, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4398 c row = (mc 1057 + mc 1530 - mc 1449*mc 1530 - 2*mc 1057*mc 1530 + 2*mc 1057*mc 1449*mc 1530) + 2 * KeccakfPermAir.extraction.inter_4396 c row := by
    simp only [KeccakfPermAir.extraction.inter_4398, KeccakfPermAir.extraction.inter_4397, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4396 c row = (mc 1058 + mc 1531 - mc 1450*mc 1531 - 2*mc 1058*mc 1531 + 2*mc 1058*mc 1450*mc 1531) + 2 * KeccakfPermAir.extraction.inter_4394 c row := by
    simp only [KeccakfPermAir.extraction.inter_4396, KeccakfPermAir.extraction.inter_4395, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4394 c row = (mc 1059 + mc 1532 - mc 1451*mc 1532 - 2*mc 1059*mc 1532 + 2*mc 1059*mc 1451*mc 1532) + 2 * KeccakfPermAir.extraction.inter_4392 c row := by
    simp only [KeccakfPermAir.extraction.inter_4394, KeccakfPermAir.extraction.inter_4393, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4392 c row = (mc 1060 + mc 1533 - mc 1452*mc 1533 - 2*mc 1060*mc 1533 + 2*mc 1060*mc 1452*mc 1533) := by
    simp only [KeccakfPermAir.extraction.inter_4392, KeccakfPermAir.extraction.inter_4391, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2932 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2932 c row) :
    ((mc 1061 + mc 1534 - mc 1453*mc 1534 - 2*mc 1061*mc 1534 + 2*mc 1061*mc 1453*mc 1534) + 2*(mc 1062 + mc 1535 - mc 1454*mc 1535 - 2*mc 1062*mc 1535 + 2*mc 1062*mc 1454*mc 1535) + 4*(mc 1063 + mc 1536 - mc 1455*mc 1536 - 2*mc 1063*mc 1536 + 2*mc 1063*mc 1455*mc 1536) + 8*(mc 1064 + mc 1537 - mc 1456*mc 1537 - 2*mc 1064*mc 1537 + 2*mc 1064*mc 1456*mc 1537) + 16*(mc 1065 + mc 1538 - mc 1457*mc 1538 - 2*mc 1065*mc 1538 + 2*mc 1065*mc 1457*mc 1538) + 32*(mc 1066 + mc 1539 - mc 1458*mc 1539 - 2*mc 1066*mc 1539 + 2*mc 1066*mc 1458*mc 1539) + 64*(mc 1067 + mc 1540 - mc 1459*mc 1540 - 2*mc 1067*mc 1540 + 2*mc 1067*mc 1459*mc 1540) + 128*(mc 1068 + mc 1541 - mc 1460*mc 1541 - 2*mc 1068*mc 1541 + 2*mc 1068*mc 1460*mc 1541) + 256*(mc 1069 + mc 1542 - mc 1461*mc 1542 - 2*mc 1069*mc 1542 + 2*mc 1069*mc 1461*mc 1542) + 512*(mc 1070 + mc 1543 - mc 1462*mc 1543 - 2*mc 1070*mc 1543 + 2*mc 1070*mc 1462*mc 1543) + 1024*(mc 1071 + mc 1544 - mc 1463*mc 1544 - 2*mc 1071*mc 1544 + 2*mc 1071*mc 1463*mc 1544) + 2048*(mc 1072 + mc 1545 - mc 1464*mc 1545 - 2*mc 1072*mc 1545 + 2*mc 1072*mc 1464*mc 1545) + 4096*(mc 1073 + mc 1546 - mc 1465*mc 1546 - 2*mc 1073*mc 1546 + 2*mc 1073*mc 1465*mc 1546) + 8192*(mc 1074 + mc 1547 - mc 1466*mc 1547 - 2*mc 1074*mc 1547 + 2*mc 1074*mc 1466*mc 1547) + 16384*(mc 1075 + mc 1548 - mc 1467*mc 1548 - 2*mc 1075*mc 1548 + 2*mc 1075*mc 1467*mc 1548) + 32768*(mc 1076 + mc 1549 - mc 1468*mc 1549 - 2*mc 1076*mc 1549 + 2*mc 1076*mc 1468*mc 1549)) - mc 2487 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2932, KeccakfPermAir.extraction.inter_4452, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4451 c row = (mc 1062 + mc 1535 - mc 1454*mc 1535 - 2*mc 1062*mc 1535 + 2*mc 1062*mc 1454*mc 1535) + 2 * KeccakfPermAir.extraction.inter_4449 c row := by
    simp only [KeccakfPermAir.extraction.inter_4451, KeccakfPermAir.extraction.inter_4450, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4449 c row = (mc 1063 + mc 1536 - mc 1455*mc 1536 - 2*mc 1063*mc 1536 + 2*mc 1063*mc 1455*mc 1536) + 2 * KeccakfPermAir.extraction.inter_4447 c row := by
    simp only [KeccakfPermAir.extraction.inter_4449, KeccakfPermAir.extraction.inter_4448, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4447 c row = (mc 1064 + mc 1537 - mc 1456*mc 1537 - 2*mc 1064*mc 1537 + 2*mc 1064*mc 1456*mc 1537) + 2 * KeccakfPermAir.extraction.inter_4445 c row := by
    simp only [KeccakfPermAir.extraction.inter_4447, KeccakfPermAir.extraction.inter_4446, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4445 c row = (mc 1065 + mc 1538 - mc 1457*mc 1538 - 2*mc 1065*mc 1538 + 2*mc 1065*mc 1457*mc 1538) + 2 * KeccakfPermAir.extraction.inter_4443 c row := by
    simp only [KeccakfPermAir.extraction.inter_4445, KeccakfPermAir.extraction.inter_4444, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4443 c row = (mc 1066 + mc 1539 - mc 1458*mc 1539 - 2*mc 1066*mc 1539 + 2*mc 1066*mc 1458*mc 1539) + 2 * KeccakfPermAir.extraction.inter_4441 c row := by
    simp only [KeccakfPermAir.extraction.inter_4443, KeccakfPermAir.extraction.inter_4442, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4441 c row = (mc 1067 + mc 1540 - mc 1459*mc 1540 - 2*mc 1067*mc 1540 + 2*mc 1067*mc 1459*mc 1540) + 2 * KeccakfPermAir.extraction.inter_4439 c row := by
    simp only [KeccakfPermAir.extraction.inter_4441, KeccakfPermAir.extraction.inter_4440, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4439 c row = (mc 1068 + mc 1541 - mc 1460*mc 1541 - 2*mc 1068*mc 1541 + 2*mc 1068*mc 1460*mc 1541) + 2 * KeccakfPermAir.extraction.inter_4437 c row := by
    simp only [KeccakfPermAir.extraction.inter_4439, KeccakfPermAir.extraction.inter_4438, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4437 c row = (mc 1069 + mc 1542 - mc 1461*mc 1542 - 2*mc 1069*mc 1542 + 2*mc 1069*mc 1461*mc 1542) + 2 * KeccakfPermAir.extraction.inter_4435 c row := by
    simp only [KeccakfPermAir.extraction.inter_4437, KeccakfPermAir.extraction.inter_4436, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4435 c row = (mc 1070 + mc 1543 - mc 1462*mc 1543 - 2*mc 1070*mc 1543 + 2*mc 1070*mc 1462*mc 1543) + 2 * KeccakfPermAir.extraction.inter_4433 c row := by
    simp only [KeccakfPermAir.extraction.inter_4435, KeccakfPermAir.extraction.inter_4434, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4433 c row = (mc 1071 + mc 1544 - mc 1463*mc 1544 - 2*mc 1071*mc 1544 + 2*mc 1071*mc 1463*mc 1544) + 2 * KeccakfPermAir.extraction.inter_4431 c row := by
    simp only [KeccakfPermAir.extraction.inter_4433, KeccakfPermAir.extraction.inter_4432, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4431 c row = (mc 1072 + mc 1545 - mc 1464*mc 1545 - 2*mc 1072*mc 1545 + 2*mc 1072*mc 1464*mc 1545) + 2 * KeccakfPermAir.extraction.inter_4429 c row := by
    simp only [KeccakfPermAir.extraction.inter_4431, KeccakfPermAir.extraction.inter_4430, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4429 c row = (mc 1073 + mc 1546 - mc 1465*mc 1546 - 2*mc 1073*mc 1546 + 2*mc 1073*mc 1465*mc 1546) + 2 * KeccakfPermAir.extraction.inter_4427 c row := by
    simp only [KeccakfPermAir.extraction.inter_4429, KeccakfPermAir.extraction.inter_4428, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4427 c row = (mc 1074 + mc 1547 - mc 1466*mc 1547 - 2*mc 1074*mc 1547 + 2*mc 1074*mc 1466*mc 1547) + 2 * KeccakfPermAir.extraction.inter_4425 c row := by
    simp only [KeccakfPermAir.extraction.inter_4427, KeccakfPermAir.extraction.inter_4426, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4425 c row = (mc 1075 + mc 1548 - mc 1467*mc 1548 - 2*mc 1075*mc 1548 + 2*mc 1075*mc 1467*mc 1548) + 2 * KeccakfPermAir.extraction.inter_4423 c row := by
    simp only [KeccakfPermAir.extraction.inter_4425, KeccakfPermAir.extraction.inter_4424, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4423 c row = (mc 1076 + mc 1549 - mc 1468*mc 1549 - 2*mc 1076*mc 1549 + 2*mc 1076*mc 1468*mc 1549) := by
    simp only [KeccakfPermAir.extraction.inter_4423, KeccakfPermAir.extraction.inter_4422, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2933 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2933 c row) :
    ((mc 1077 + mc 1550 - mc 1469*mc 1550 - 2*mc 1077*mc 1550 + 2*mc 1077*mc 1469*mc 1550) + 2*(mc 1078 + mc 1551 - mc 1470*mc 1551 - 2*mc 1078*mc 1551 + 2*mc 1078*mc 1470*mc 1551) + 4*(mc 1079 + mc 1552 - mc 1471*mc 1552 - 2*mc 1079*mc 1552 + 2*mc 1079*mc 1471*mc 1552) + 8*(mc 1080 + mc 1553 - mc 1472*mc 1553 - 2*mc 1080*mc 1553 + 2*mc 1080*mc 1472*mc 1553) + 16*(mc 1081 + mc 1554 - mc 1473*mc 1554 - 2*mc 1081*mc 1554 + 2*mc 1081*mc 1473*mc 1554) + 32*(mc 1082 + mc 1555 - mc 1474*mc 1555 - 2*mc 1082*mc 1555 + 2*mc 1082*mc 1474*mc 1555) + 64*(mc 1083 + mc 1556 - mc 1475*mc 1556 - 2*mc 1083*mc 1556 + 2*mc 1083*mc 1475*mc 1556) + 128*(mc 1084 + mc 1557 - mc 1476*mc 1557 - 2*mc 1084*mc 1557 + 2*mc 1084*mc 1476*mc 1557) + 256*(mc 1085 + mc 1558 - mc 1477*mc 1558 - 2*mc 1085*mc 1558 + 2*mc 1085*mc 1477*mc 1558) + 512*(mc 1086 + mc 1559 - mc 1478*mc 1559 - 2*mc 1086*mc 1559 + 2*mc 1086*mc 1478*mc 1559) + 1024*(mc 1087 + mc 1560 - mc 1479*mc 1560 - 2*mc 1087*mc 1560 + 2*mc 1087*mc 1479*mc 1560) + 2048*(mc 1088 + mc 1561 - mc 1480*mc 1561 - 2*mc 1088*mc 1561 + 2*mc 1088*mc 1480*mc 1561) + 4096*(mc 1089 + mc 1562 - mc 1481*mc 1562 - 2*mc 1089*mc 1562 + 2*mc 1089*mc 1481*mc 1562) + 8192*(mc 1090 + mc 1563 - mc 1482*mc 1563 - 2*mc 1090*mc 1563 + 2*mc 1090*mc 1482*mc 1563) + 16384*(mc 1091 + mc 1564 - mc 1483*mc 1564 - 2*mc 1091*mc 1564 + 2*mc 1091*mc 1483*mc 1564) + 32768*(mc 1092 + mc 1565 - mc 1484*mc 1565 - 2*mc 1092*mc 1565 + 2*mc 1092*mc 1484*mc 1565)) - mc 2488 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2933, KeccakfPermAir.extraction.inter_4483, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4482 c row = (mc 1078 + mc 1551 - mc 1470*mc 1551 - 2*mc 1078*mc 1551 + 2*mc 1078*mc 1470*mc 1551) + 2 * KeccakfPermAir.extraction.inter_4480 c row := by
    simp only [KeccakfPermAir.extraction.inter_4482, KeccakfPermAir.extraction.inter_4481, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4480 c row = (mc 1079 + mc 1552 - mc 1471*mc 1552 - 2*mc 1079*mc 1552 + 2*mc 1079*mc 1471*mc 1552) + 2 * KeccakfPermAir.extraction.inter_4478 c row := by
    simp only [KeccakfPermAir.extraction.inter_4480, KeccakfPermAir.extraction.inter_4479, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4478 c row = (mc 1080 + mc 1553 - mc 1472*mc 1553 - 2*mc 1080*mc 1553 + 2*mc 1080*mc 1472*mc 1553) + 2 * KeccakfPermAir.extraction.inter_4476 c row := by
    simp only [KeccakfPermAir.extraction.inter_4478, KeccakfPermAir.extraction.inter_4477, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4476 c row = (mc 1081 + mc 1554 - mc 1473*mc 1554 - 2*mc 1081*mc 1554 + 2*mc 1081*mc 1473*mc 1554) + 2 * KeccakfPermAir.extraction.inter_4474 c row := by
    simp only [KeccakfPermAir.extraction.inter_4476, KeccakfPermAir.extraction.inter_4475, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4474 c row = (mc 1082 + mc 1555 - mc 1474*mc 1555 - 2*mc 1082*mc 1555 + 2*mc 1082*mc 1474*mc 1555) + 2 * KeccakfPermAir.extraction.inter_4472 c row := by
    simp only [KeccakfPermAir.extraction.inter_4474, KeccakfPermAir.extraction.inter_4473, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4472 c row = (mc 1083 + mc 1556 - mc 1475*mc 1556 - 2*mc 1083*mc 1556 + 2*mc 1083*mc 1475*mc 1556) + 2 * KeccakfPermAir.extraction.inter_4470 c row := by
    simp only [KeccakfPermAir.extraction.inter_4472, KeccakfPermAir.extraction.inter_4471, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4470 c row = (mc 1084 + mc 1557 - mc 1476*mc 1557 - 2*mc 1084*mc 1557 + 2*mc 1084*mc 1476*mc 1557) + 2 * KeccakfPermAir.extraction.inter_4468 c row := by
    simp only [KeccakfPermAir.extraction.inter_4470, KeccakfPermAir.extraction.inter_4469, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4468 c row = (mc 1085 + mc 1558 - mc 1477*mc 1558 - 2*mc 1085*mc 1558 + 2*mc 1085*mc 1477*mc 1558) + 2 * KeccakfPermAir.extraction.inter_4466 c row := by
    simp only [KeccakfPermAir.extraction.inter_4468, KeccakfPermAir.extraction.inter_4467, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4466 c row = (mc 1086 + mc 1559 - mc 1478*mc 1559 - 2*mc 1086*mc 1559 + 2*mc 1086*mc 1478*mc 1559) + 2 * KeccakfPermAir.extraction.inter_4464 c row := by
    simp only [KeccakfPermAir.extraction.inter_4466, KeccakfPermAir.extraction.inter_4465, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4464 c row = (mc 1087 + mc 1560 - mc 1479*mc 1560 - 2*mc 1087*mc 1560 + 2*mc 1087*mc 1479*mc 1560) + 2 * KeccakfPermAir.extraction.inter_4462 c row := by
    simp only [KeccakfPermAir.extraction.inter_4464, KeccakfPermAir.extraction.inter_4463, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4462 c row = (mc 1088 + mc 1561 - mc 1480*mc 1561 - 2*mc 1088*mc 1561 + 2*mc 1088*mc 1480*mc 1561) + 2 * KeccakfPermAir.extraction.inter_4460 c row := by
    simp only [KeccakfPermAir.extraction.inter_4462, KeccakfPermAir.extraction.inter_4461, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4460 c row = (mc 1089 + mc 1562 - mc 1481*mc 1562 - 2*mc 1089*mc 1562 + 2*mc 1089*mc 1481*mc 1562) + 2 * KeccakfPermAir.extraction.inter_4458 c row := by
    simp only [KeccakfPermAir.extraction.inter_4460, KeccakfPermAir.extraction.inter_4459, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4458 c row = (mc 1090 + mc 1563 - mc 1482*mc 1563 - 2*mc 1090*mc 1563 + 2*mc 1090*mc 1482*mc 1563) + 2 * KeccakfPermAir.extraction.inter_4456 c row := by
    simp only [KeccakfPermAir.extraction.inter_4458, KeccakfPermAir.extraction.inter_4457, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4456 c row = (mc 1091 + mc 1564 - mc 1483*mc 1564 - 2*mc 1091*mc 1564 + 2*mc 1091*mc 1483*mc 1564) + 2 * KeccakfPermAir.extraction.inter_4454 c row := by
    simp only [KeccakfPermAir.extraction.inter_4456, KeccakfPermAir.extraction.inter_4455, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4454 c row = (mc 1092 + mc 1565 - mc 1484*mc 1565 - 2*mc 1092*mc 1565 + 2*mc 1092*mc 1484*mc 1565) := by
    simp only [KeccakfPermAir.extraction.inter_4454, KeccakfPermAir.extraction.inter_4453, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2934 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2934 c row) :
    ((mc 1485 + mc 1908 - mc 1566*mc 1908 - 2*mc 1485*mc 1908 + 2*mc 1485*mc 1566*mc 1908) + 2*(mc 1486 + mc 1909 - mc 1567*mc 1909 - 2*mc 1486*mc 1909 + 2*mc 1486*mc 1567*mc 1909) + 4*(mc 1487 + mc 1910 - mc 1568*mc 1910 - 2*mc 1487*mc 1910 + 2*mc 1487*mc 1568*mc 1910) + 8*(mc 1488 + mc 1911 - mc 1505*mc 1911 - 2*mc 1488*mc 1911 + 2*mc 1488*mc 1505*mc 1911) + 16*(mc 1489 + mc 1912 - mc 1506*mc 1912 - 2*mc 1489*mc 1912 + 2*mc 1489*mc 1506*mc 1912) + 32*(mc 1490 + mc 1913 - mc 1507*mc 1913 - 2*mc 1490*mc 1913 + 2*mc 1490*mc 1507*mc 1913) + 64*(mc 1491 + mc 1914 - mc 1508*mc 1914 - 2*mc 1491*mc 1914 + 2*mc 1491*mc 1508*mc 1914) + 128*(mc 1492 + mc 1915 - mc 1509*mc 1915 - 2*mc 1492*mc 1915 + 2*mc 1492*mc 1509*mc 1915) + 256*(mc 1493 + mc 1916 - mc 1510*mc 1916 - 2*mc 1493*mc 1916 + 2*mc 1493*mc 1510*mc 1916) + 512*(mc 1494 + mc 1917 - mc 1511*mc 1917 - 2*mc 1494*mc 1917 + 2*mc 1494*mc 1511*mc 1917) + 1024*(mc 1495 + mc 1918 - mc 1512*mc 1918 - 2*mc 1495*mc 1918 + 2*mc 1495*mc 1512*mc 1918) + 2048*(mc 1496 + mc 1919 - mc 1513*mc 1919 - 2*mc 1496*mc 1919 + 2*mc 1496*mc 1513*mc 1919) + 4096*(mc 1497 + mc 1920 - mc 1514*mc 1920 - 2*mc 1497*mc 1920 + 2*mc 1497*mc 1514*mc 1920) + 8192*(mc 1498 + mc 1921 - mc 1515*mc 1921 - 2*mc 1498*mc 1921 + 2*mc 1498*mc 1515*mc 1921) + 16384*(mc 1499 + mc 1922 - mc 1516*mc 1922 - 2*mc 1499*mc 1922 + 2*mc 1499*mc 1516*mc 1922) + 32768*(mc 1500 + mc 1923 - mc 1517*mc 1923 - 2*mc 1500*mc 1923 + 2*mc 1500*mc 1517*mc 1923)) - mc 2489 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2934, KeccakfPermAir.extraction.inter_4514, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4513 c row = (mc 1486 + mc 1909 - mc 1567*mc 1909 - 2*mc 1486*mc 1909 + 2*mc 1486*mc 1567*mc 1909) + 2 * KeccakfPermAir.extraction.inter_4511 c row := by
    simp only [KeccakfPermAir.extraction.inter_4513, KeccakfPermAir.extraction.inter_4512, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4511 c row = (mc 1487 + mc 1910 - mc 1568*mc 1910 - 2*mc 1487*mc 1910 + 2*mc 1487*mc 1568*mc 1910) + 2 * KeccakfPermAir.extraction.inter_4509 c row := by
    simp only [KeccakfPermAir.extraction.inter_4511, KeccakfPermAir.extraction.inter_4510, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4509 c row = (mc 1488 + mc 1911 - mc 1505*mc 1911 - 2*mc 1488*mc 1911 + 2*mc 1488*mc 1505*mc 1911) + 2 * KeccakfPermAir.extraction.inter_4507 c row := by
    simp only [KeccakfPermAir.extraction.inter_4509, KeccakfPermAir.extraction.inter_4508, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4507 c row = (mc 1489 + mc 1912 - mc 1506*mc 1912 - 2*mc 1489*mc 1912 + 2*mc 1489*mc 1506*mc 1912) + 2 * KeccakfPermAir.extraction.inter_4505 c row := by
    simp only [KeccakfPermAir.extraction.inter_4507, KeccakfPermAir.extraction.inter_4506, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4505 c row = (mc 1490 + mc 1913 - mc 1507*mc 1913 - 2*mc 1490*mc 1913 + 2*mc 1490*mc 1507*mc 1913) + 2 * KeccakfPermAir.extraction.inter_4503 c row := by
    simp only [KeccakfPermAir.extraction.inter_4505, KeccakfPermAir.extraction.inter_4504, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4503 c row = (mc 1491 + mc 1914 - mc 1508*mc 1914 - 2*mc 1491*mc 1914 + 2*mc 1491*mc 1508*mc 1914) + 2 * KeccakfPermAir.extraction.inter_4501 c row := by
    simp only [KeccakfPermAir.extraction.inter_4503, KeccakfPermAir.extraction.inter_4502, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4501 c row = (mc 1492 + mc 1915 - mc 1509*mc 1915 - 2*mc 1492*mc 1915 + 2*mc 1492*mc 1509*mc 1915) + 2 * KeccakfPermAir.extraction.inter_4499 c row := by
    simp only [KeccakfPermAir.extraction.inter_4501, KeccakfPermAir.extraction.inter_4500, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4499 c row = (mc 1493 + mc 1916 - mc 1510*mc 1916 - 2*mc 1493*mc 1916 + 2*mc 1493*mc 1510*mc 1916) + 2 * KeccakfPermAir.extraction.inter_4497 c row := by
    simp only [KeccakfPermAir.extraction.inter_4499, KeccakfPermAir.extraction.inter_4498, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4497 c row = (mc 1494 + mc 1917 - mc 1511*mc 1917 - 2*mc 1494*mc 1917 + 2*mc 1494*mc 1511*mc 1917) + 2 * KeccakfPermAir.extraction.inter_4495 c row := by
    simp only [KeccakfPermAir.extraction.inter_4497, KeccakfPermAir.extraction.inter_4496, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4495 c row = (mc 1495 + mc 1918 - mc 1512*mc 1918 - 2*mc 1495*mc 1918 + 2*mc 1495*mc 1512*mc 1918) + 2 * KeccakfPermAir.extraction.inter_4493 c row := by
    simp only [KeccakfPermAir.extraction.inter_4495, KeccakfPermAir.extraction.inter_4494, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4493 c row = (mc 1496 + mc 1919 - mc 1513*mc 1919 - 2*mc 1496*mc 1919 + 2*mc 1496*mc 1513*mc 1919) + 2 * KeccakfPermAir.extraction.inter_4491 c row := by
    simp only [KeccakfPermAir.extraction.inter_4493, KeccakfPermAir.extraction.inter_4492, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4491 c row = (mc 1497 + mc 1920 - mc 1514*mc 1920 - 2*mc 1497*mc 1920 + 2*mc 1497*mc 1514*mc 1920) + 2 * KeccakfPermAir.extraction.inter_4489 c row := by
    simp only [KeccakfPermAir.extraction.inter_4491, KeccakfPermAir.extraction.inter_4490, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4489 c row = (mc 1498 + mc 1921 - mc 1515*mc 1921 - 2*mc 1498*mc 1921 + 2*mc 1498*mc 1515*mc 1921) + 2 * KeccakfPermAir.extraction.inter_4487 c row := by
    simp only [KeccakfPermAir.extraction.inter_4489, KeccakfPermAir.extraction.inter_4488, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4487 c row = (mc 1499 + mc 1922 - mc 1516*mc 1922 - 2*mc 1499*mc 1922 + 2*mc 1499*mc 1516*mc 1922) + 2 * KeccakfPermAir.extraction.inter_4485 c row := by
    simp only [KeccakfPermAir.extraction.inter_4487, KeccakfPermAir.extraction.inter_4486, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4485 c row = (mc 1500 + mc 1923 - mc 1517*mc 1923 - 2*mc 1500*mc 1923 + 2*mc 1500*mc 1517*mc 1923) := by
    simp only [KeccakfPermAir.extraction.inter_4485, KeccakfPermAir.extraction.inter_4484, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2935 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2935 c row) :
    ((mc 1501 + mc 1924 - mc 1518*mc 1924 - 2*mc 1501*mc 1924 + 2*mc 1501*mc 1518*mc 1924) + 2*(mc 1502 + mc 1925 - mc 1519*mc 1925 - 2*mc 1502*mc 1925 + 2*mc 1502*mc 1519*mc 1925) + 4*(mc 1503 + mc 1926 - mc 1520*mc 1926 - 2*mc 1503*mc 1926 + 2*mc 1503*mc 1520*mc 1926) + 8*(mc 1504 + mc 1927 - mc 1521*mc 1927 - 2*mc 1504*mc 1927 + 2*mc 1504*mc 1521*mc 1927) + 16*(mc 1441 + mc 1928 - mc 1522*mc 1928 - 2*mc 1441*mc 1928 + 2*mc 1441*mc 1522*mc 1928) + 32*(mc 1442 + mc 1929 - mc 1523*mc 1929 - 2*mc 1442*mc 1929 + 2*mc 1442*mc 1523*mc 1929) + 64*(mc 1443 + mc 1930 - mc 1524*mc 1930 - 2*mc 1443*mc 1930 + 2*mc 1443*mc 1524*mc 1930) + 128*(mc 1444 + mc 1931 - mc 1525*mc 1931 - 2*mc 1444*mc 1931 + 2*mc 1444*mc 1525*mc 1931) + 256*(mc 1445 + mc 1932 - mc 1526*mc 1932 - 2*mc 1445*mc 1932 + 2*mc 1445*mc 1526*mc 1932) + 512*(mc 1446 + mc 1933 - mc 1527*mc 1933 - 2*mc 1446*mc 1933 + 2*mc 1446*mc 1527*mc 1933) + 1024*(mc 1447 + mc 1934 - mc 1528*mc 1934 - 2*mc 1447*mc 1934 + 2*mc 1447*mc 1528*mc 1934) + 2048*(mc 1448 + mc 1935 - mc 1529*mc 1935 - 2*mc 1448*mc 1935 + 2*mc 1448*mc 1529*mc 1935) + 4096*(mc 1449 + mc 1936 - mc 1530*mc 1936 - 2*mc 1449*mc 1936 + 2*mc 1449*mc 1530*mc 1936) + 8192*(mc 1450 + mc 1937 - mc 1531*mc 1937 - 2*mc 1450*mc 1937 + 2*mc 1450*mc 1531*mc 1937) + 16384*(mc 1451 + mc 1938 - mc 1532*mc 1938 - 2*mc 1451*mc 1938 + 2*mc 1451*mc 1532*mc 1938) + 32768*(mc 1452 + mc 1939 - mc 1533*mc 1939 - 2*mc 1452*mc 1939 + 2*mc 1452*mc 1533*mc 1939)) - mc 2490 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2935, KeccakfPermAir.extraction.inter_4545, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4544 c row = (mc 1502 + mc 1925 - mc 1519*mc 1925 - 2*mc 1502*mc 1925 + 2*mc 1502*mc 1519*mc 1925) + 2 * KeccakfPermAir.extraction.inter_4542 c row := by
    simp only [KeccakfPermAir.extraction.inter_4544, KeccakfPermAir.extraction.inter_4543, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4542 c row = (mc 1503 + mc 1926 - mc 1520*mc 1926 - 2*mc 1503*mc 1926 + 2*mc 1503*mc 1520*mc 1926) + 2 * KeccakfPermAir.extraction.inter_4540 c row := by
    simp only [KeccakfPermAir.extraction.inter_4542, KeccakfPermAir.extraction.inter_4541, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4540 c row = (mc 1504 + mc 1927 - mc 1521*mc 1927 - 2*mc 1504*mc 1927 + 2*mc 1504*mc 1521*mc 1927) + 2 * KeccakfPermAir.extraction.inter_4538 c row := by
    simp only [KeccakfPermAir.extraction.inter_4540, KeccakfPermAir.extraction.inter_4539, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4538 c row = (mc 1441 + mc 1928 - mc 1522*mc 1928 - 2*mc 1441*mc 1928 + 2*mc 1441*mc 1522*mc 1928) + 2 * KeccakfPermAir.extraction.inter_4536 c row := by
    simp only [KeccakfPermAir.extraction.inter_4538, KeccakfPermAir.extraction.inter_4537, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4536 c row = (mc 1442 + mc 1929 - mc 1523*mc 1929 - 2*mc 1442*mc 1929 + 2*mc 1442*mc 1523*mc 1929) + 2 * KeccakfPermAir.extraction.inter_4534 c row := by
    simp only [KeccakfPermAir.extraction.inter_4536, KeccakfPermAir.extraction.inter_4535, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4534 c row = (mc 1443 + mc 1930 - mc 1524*mc 1930 - 2*mc 1443*mc 1930 + 2*mc 1443*mc 1524*mc 1930) + 2 * KeccakfPermAir.extraction.inter_4532 c row := by
    simp only [KeccakfPermAir.extraction.inter_4534, KeccakfPermAir.extraction.inter_4533, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4532 c row = (mc 1444 + mc 1931 - mc 1525*mc 1931 - 2*mc 1444*mc 1931 + 2*mc 1444*mc 1525*mc 1931) + 2 * KeccakfPermAir.extraction.inter_4530 c row := by
    simp only [KeccakfPermAir.extraction.inter_4532, KeccakfPermAir.extraction.inter_4531, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4530 c row = (mc 1445 + mc 1932 - mc 1526*mc 1932 - 2*mc 1445*mc 1932 + 2*mc 1445*mc 1526*mc 1932) + 2 * KeccakfPermAir.extraction.inter_4528 c row := by
    simp only [KeccakfPermAir.extraction.inter_4530, KeccakfPermAir.extraction.inter_4529, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4528 c row = (mc 1446 + mc 1933 - mc 1527*mc 1933 - 2*mc 1446*mc 1933 + 2*mc 1446*mc 1527*mc 1933) + 2 * KeccakfPermAir.extraction.inter_4526 c row := by
    simp only [KeccakfPermAir.extraction.inter_4528, KeccakfPermAir.extraction.inter_4527, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4526 c row = (mc 1447 + mc 1934 - mc 1528*mc 1934 - 2*mc 1447*mc 1934 + 2*mc 1447*mc 1528*mc 1934) + 2 * KeccakfPermAir.extraction.inter_4524 c row := by
    simp only [KeccakfPermAir.extraction.inter_4526, KeccakfPermAir.extraction.inter_4525, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4524 c row = (mc 1448 + mc 1935 - mc 1529*mc 1935 - 2*mc 1448*mc 1935 + 2*mc 1448*mc 1529*mc 1935) + 2 * KeccakfPermAir.extraction.inter_4522 c row := by
    simp only [KeccakfPermAir.extraction.inter_4524, KeccakfPermAir.extraction.inter_4523, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4522 c row = (mc 1449 + mc 1936 - mc 1530*mc 1936 - 2*mc 1449*mc 1936 + 2*mc 1449*mc 1530*mc 1936) + 2 * KeccakfPermAir.extraction.inter_4520 c row := by
    simp only [KeccakfPermAir.extraction.inter_4522, KeccakfPermAir.extraction.inter_4521, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4520 c row = (mc 1450 + mc 1937 - mc 1531*mc 1937 - 2*mc 1450*mc 1937 + 2*mc 1450*mc 1531*mc 1937) + 2 * KeccakfPermAir.extraction.inter_4518 c row := by
    simp only [KeccakfPermAir.extraction.inter_4520, KeccakfPermAir.extraction.inter_4519, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4518 c row = (mc 1451 + mc 1938 - mc 1532*mc 1938 - 2*mc 1451*mc 1938 + 2*mc 1451*mc 1532*mc 1938) + 2 * KeccakfPermAir.extraction.inter_4516 c row := by
    simp only [KeccakfPermAir.extraction.inter_4518, KeccakfPermAir.extraction.inter_4517, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4516 c row = (mc 1452 + mc 1939 - mc 1533*mc 1939 - 2*mc 1452*mc 1939 + 2*mc 1452*mc 1533*mc 1939) := by
    simp only [KeccakfPermAir.extraction.inter_4516, KeccakfPermAir.extraction.inter_4515, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2936 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2936 c row) :
    ((mc 1453 + mc 1940 - mc 1534*mc 1940 - 2*mc 1453*mc 1940 + 2*mc 1453*mc 1534*mc 1940) + 2*(mc 1454 + mc 1941 - mc 1535*mc 1941 - 2*mc 1454*mc 1941 + 2*mc 1454*mc 1535*mc 1941) + 4*(mc 1455 + mc 1942 - mc 1536*mc 1942 - 2*mc 1455*mc 1942 + 2*mc 1455*mc 1536*mc 1942) + 8*(mc 1456 + mc 1943 - mc 1537*mc 1943 - 2*mc 1456*mc 1943 + 2*mc 1456*mc 1537*mc 1943) + 16*(mc 1457 + mc 1944 - mc 1538*mc 1944 - 2*mc 1457*mc 1944 + 2*mc 1457*mc 1538*mc 1944) + 32*(mc 1458 + mc 1945 - mc 1539*mc 1945 - 2*mc 1458*mc 1945 + 2*mc 1458*mc 1539*mc 1945) + 64*(mc 1459 + mc 1946 - mc 1540*mc 1946 - 2*mc 1459*mc 1946 + 2*mc 1459*mc 1540*mc 1946) + 128*(mc 1460 + mc 1947 - mc 1541*mc 1947 - 2*mc 1460*mc 1947 + 2*mc 1460*mc 1541*mc 1947) + 256*(mc 1461 + mc 1948 - mc 1542*mc 1948 - 2*mc 1461*mc 1948 + 2*mc 1461*mc 1542*mc 1948) + 512*(mc 1462 + mc 1949 - mc 1543*mc 1949 - 2*mc 1462*mc 1949 + 2*mc 1462*mc 1543*mc 1949) + 1024*(mc 1463 + mc 1950 - mc 1544*mc 1950 - 2*mc 1463*mc 1950 + 2*mc 1463*mc 1544*mc 1950) + 2048*(mc 1464 + mc 1951 - mc 1545*mc 1951 - 2*mc 1464*mc 1951 + 2*mc 1464*mc 1545*mc 1951) + 4096*(mc 1465 + mc 1952 - mc 1546*mc 1952 - 2*mc 1465*mc 1952 + 2*mc 1465*mc 1546*mc 1952) + 8192*(mc 1466 + mc 1889 - mc 1547*mc 1889 - 2*mc 1466*mc 1889 + 2*mc 1466*mc 1547*mc 1889) + 16384*(mc 1467 + mc 1890 - mc 1548*mc 1890 - 2*mc 1467*mc 1890 + 2*mc 1467*mc 1548*mc 1890) + 32768*(mc 1468 + mc 1891 - mc 1549*mc 1891 - 2*mc 1468*mc 1891 + 2*mc 1468*mc 1549*mc 1891)) - mc 2491 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2936, KeccakfPermAir.extraction.inter_4576, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4575 c row = (mc 1454 + mc 1941 - mc 1535*mc 1941 - 2*mc 1454*mc 1941 + 2*mc 1454*mc 1535*mc 1941) + 2 * KeccakfPermAir.extraction.inter_4573 c row := by
    simp only [KeccakfPermAir.extraction.inter_4575, KeccakfPermAir.extraction.inter_4574, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4573 c row = (mc 1455 + mc 1942 - mc 1536*mc 1942 - 2*mc 1455*mc 1942 + 2*mc 1455*mc 1536*mc 1942) + 2 * KeccakfPermAir.extraction.inter_4571 c row := by
    simp only [KeccakfPermAir.extraction.inter_4573, KeccakfPermAir.extraction.inter_4572, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4571 c row = (mc 1456 + mc 1943 - mc 1537*mc 1943 - 2*mc 1456*mc 1943 + 2*mc 1456*mc 1537*mc 1943) + 2 * KeccakfPermAir.extraction.inter_4569 c row := by
    simp only [KeccakfPermAir.extraction.inter_4571, KeccakfPermAir.extraction.inter_4570, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4569 c row = (mc 1457 + mc 1944 - mc 1538*mc 1944 - 2*mc 1457*mc 1944 + 2*mc 1457*mc 1538*mc 1944) + 2 * KeccakfPermAir.extraction.inter_4567 c row := by
    simp only [KeccakfPermAir.extraction.inter_4569, KeccakfPermAir.extraction.inter_4568, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4567 c row = (mc 1458 + mc 1945 - mc 1539*mc 1945 - 2*mc 1458*mc 1945 + 2*mc 1458*mc 1539*mc 1945) + 2 * KeccakfPermAir.extraction.inter_4565 c row := by
    simp only [KeccakfPermAir.extraction.inter_4567, KeccakfPermAir.extraction.inter_4566, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4565 c row = (mc 1459 + mc 1946 - mc 1540*mc 1946 - 2*mc 1459*mc 1946 + 2*mc 1459*mc 1540*mc 1946) + 2 * KeccakfPermAir.extraction.inter_4563 c row := by
    simp only [KeccakfPermAir.extraction.inter_4565, KeccakfPermAir.extraction.inter_4564, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4563 c row = (mc 1460 + mc 1947 - mc 1541*mc 1947 - 2*mc 1460*mc 1947 + 2*mc 1460*mc 1541*mc 1947) + 2 * KeccakfPermAir.extraction.inter_4561 c row := by
    simp only [KeccakfPermAir.extraction.inter_4563, KeccakfPermAir.extraction.inter_4562, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4561 c row = (mc 1461 + mc 1948 - mc 1542*mc 1948 - 2*mc 1461*mc 1948 + 2*mc 1461*mc 1542*mc 1948) + 2 * KeccakfPermAir.extraction.inter_4559 c row := by
    simp only [KeccakfPermAir.extraction.inter_4561, KeccakfPermAir.extraction.inter_4560, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4559 c row = (mc 1462 + mc 1949 - mc 1543*mc 1949 - 2*mc 1462*mc 1949 + 2*mc 1462*mc 1543*mc 1949) + 2 * KeccakfPermAir.extraction.inter_4557 c row := by
    simp only [KeccakfPermAir.extraction.inter_4559, KeccakfPermAir.extraction.inter_4558, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4557 c row = (mc 1463 + mc 1950 - mc 1544*mc 1950 - 2*mc 1463*mc 1950 + 2*mc 1463*mc 1544*mc 1950) + 2 * KeccakfPermAir.extraction.inter_4555 c row := by
    simp only [KeccakfPermAir.extraction.inter_4557, KeccakfPermAir.extraction.inter_4556, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4555 c row = (mc 1464 + mc 1951 - mc 1545*mc 1951 - 2*mc 1464*mc 1951 + 2*mc 1464*mc 1545*mc 1951) + 2 * KeccakfPermAir.extraction.inter_4553 c row := by
    simp only [KeccakfPermAir.extraction.inter_4555, KeccakfPermAir.extraction.inter_4554, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4553 c row = (mc 1465 + mc 1952 - mc 1546*mc 1952 - 2*mc 1465*mc 1952 + 2*mc 1465*mc 1546*mc 1952) + 2 * KeccakfPermAir.extraction.inter_4551 c row := by
    simp only [KeccakfPermAir.extraction.inter_4553, KeccakfPermAir.extraction.inter_4552, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4551 c row = (mc 1466 + mc 1889 - mc 1547*mc 1889 - 2*mc 1466*mc 1889 + 2*mc 1466*mc 1547*mc 1889) + 2 * KeccakfPermAir.extraction.inter_4549 c row := by
    simp only [KeccakfPermAir.extraction.inter_4551, KeccakfPermAir.extraction.inter_4550, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4549 c row = (mc 1467 + mc 1890 - mc 1548*mc 1890 - 2*mc 1467*mc 1890 + 2*mc 1467*mc 1548*mc 1890) + 2 * KeccakfPermAir.extraction.inter_4547 c row := by
    simp only [KeccakfPermAir.extraction.inter_4549, KeccakfPermAir.extraction.inter_4548, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4547 c row = (mc 1468 + mc 1891 - mc 1549*mc 1891 - 2*mc 1468*mc 1891 + 2*mc 1468*mc 1549*mc 1891) := by
    simp only [KeccakfPermAir.extraction.inter_4547, KeccakfPermAir.extraction.inter_4546, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2937 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2937 c row) :
    ((mc 1469 + mc 1892 - mc 1550*mc 1892 - 2*mc 1469*mc 1892 + 2*mc 1469*mc 1550*mc 1892) + 2*(mc 1470 + mc 1893 - mc 1551*mc 1893 - 2*mc 1470*mc 1893 + 2*mc 1470*mc 1551*mc 1893) + 4*(mc 1471 + mc 1894 - mc 1552*mc 1894 - 2*mc 1471*mc 1894 + 2*mc 1471*mc 1552*mc 1894) + 8*(mc 1472 + mc 1895 - mc 1553*mc 1895 - 2*mc 1472*mc 1895 + 2*mc 1472*mc 1553*mc 1895) + 16*(mc 1473 + mc 1896 - mc 1554*mc 1896 - 2*mc 1473*mc 1896 + 2*mc 1473*mc 1554*mc 1896) + 32*(mc 1474 + mc 1897 - mc 1555*mc 1897 - 2*mc 1474*mc 1897 + 2*mc 1474*mc 1555*mc 1897) + 64*(mc 1475 + mc 1898 - mc 1556*mc 1898 - 2*mc 1475*mc 1898 + 2*mc 1475*mc 1556*mc 1898) + 128*(mc 1476 + mc 1899 - mc 1557*mc 1899 - 2*mc 1476*mc 1899 + 2*mc 1476*mc 1557*mc 1899) + 256*(mc 1477 + mc 1900 - mc 1558*mc 1900 - 2*mc 1477*mc 1900 + 2*mc 1477*mc 1558*mc 1900) + 512*(mc 1478 + mc 1901 - mc 1559*mc 1901 - 2*mc 1478*mc 1901 + 2*mc 1478*mc 1559*mc 1901) + 1024*(mc 1479 + mc 1902 - mc 1560*mc 1902 - 2*mc 1479*mc 1902 + 2*mc 1479*mc 1560*mc 1902) + 2048*(mc 1480 + mc 1903 - mc 1561*mc 1903 - 2*mc 1480*mc 1903 + 2*mc 1480*mc 1561*mc 1903) + 4096*(mc 1481 + mc 1904 - mc 1562*mc 1904 - 2*mc 1481*mc 1904 + 2*mc 1481*mc 1562*mc 1904) + 8192*(mc 1482 + mc 1905 - mc 1563*mc 1905 - 2*mc 1482*mc 1905 + 2*mc 1482*mc 1563*mc 1905) + 16384*(mc 1483 + mc 1906 - mc 1564*mc 1906 - 2*mc 1483*mc 1906 + 2*mc 1483*mc 1564*mc 1906) + 32768*(mc 1484 + mc 1907 - mc 1565*mc 1907 - 2*mc 1484*mc 1907 + 2*mc 1484*mc 1565*mc 1907)) - mc 2492 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2937, KeccakfPermAir.extraction.inter_4607, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4606 c row = (mc 1470 + mc 1893 - mc 1551*mc 1893 - 2*mc 1470*mc 1893 + 2*mc 1470*mc 1551*mc 1893) + 2 * KeccakfPermAir.extraction.inter_4604 c row := by
    simp only [KeccakfPermAir.extraction.inter_4606, KeccakfPermAir.extraction.inter_4605, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4604 c row = (mc 1471 + mc 1894 - mc 1552*mc 1894 - 2*mc 1471*mc 1894 + 2*mc 1471*mc 1552*mc 1894) + 2 * KeccakfPermAir.extraction.inter_4602 c row := by
    simp only [KeccakfPermAir.extraction.inter_4604, KeccakfPermAir.extraction.inter_4603, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4602 c row = (mc 1472 + mc 1895 - mc 1553*mc 1895 - 2*mc 1472*mc 1895 + 2*mc 1472*mc 1553*mc 1895) + 2 * KeccakfPermAir.extraction.inter_4600 c row := by
    simp only [KeccakfPermAir.extraction.inter_4602, KeccakfPermAir.extraction.inter_4601, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4600 c row = (mc 1473 + mc 1896 - mc 1554*mc 1896 - 2*mc 1473*mc 1896 + 2*mc 1473*mc 1554*mc 1896) + 2 * KeccakfPermAir.extraction.inter_4598 c row := by
    simp only [KeccakfPermAir.extraction.inter_4600, KeccakfPermAir.extraction.inter_4599, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4598 c row = (mc 1474 + mc 1897 - mc 1555*mc 1897 - 2*mc 1474*mc 1897 + 2*mc 1474*mc 1555*mc 1897) + 2 * KeccakfPermAir.extraction.inter_4596 c row := by
    simp only [KeccakfPermAir.extraction.inter_4598, KeccakfPermAir.extraction.inter_4597, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4596 c row = (mc 1475 + mc 1898 - mc 1556*mc 1898 - 2*mc 1475*mc 1898 + 2*mc 1475*mc 1556*mc 1898) + 2 * KeccakfPermAir.extraction.inter_4594 c row := by
    simp only [KeccakfPermAir.extraction.inter_4596, KeccakfPermAir.extraction.inter_4595, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4594 c row = (mc 1476 + mc 1899 - mc 1557*mc 1899 - 2*mc 1476*mc 1899 + 2*mc 1476*mc 1557*mc 1899) + 2 * KeccakfPermAir.extraction.inter_4592 c row := by
    simp only [KeccakfPermAir.extraction.inter_4594, KeccakfPermAir.extraction.inter_4593, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4592 c row = (mc 1477 + mc 1900 - mc 1558*mc 1900 - 2*mc 1477*mc 1900 + 2*mc 1477*mc 1558*mc 1900) + 2 * KeccakfPermAir.extraction.inter_4590 c row := by
    simp only [KeccakfPermAir.extraction.inter_4592, KeccakfPermAir.extraction.inter_4591, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4590 c row = (mc 1478 + mc 1901 - mc 1559*mc 1901 - 2*mc 1478*mc 1901 + 2*mc 1478*mc 1559*mc 1901) + 2 * KeccakfPermAir.extraction.inter_4588 c row := by
    simp only [KeccakfPermAir.extraction.inter_4590, KeccakfPermAir.extraction.inter_4589, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4588 c row = (mc 1479 + mc 1902 - mc 1560*mc 1902 - 2*mc 1479*mc 1902 + 2*mc 1479*mc 1560*mc 1902) + 2 * KeccakfPermAir.extraction.inter_4586 c row := by
    simp only [KeccakfPermAir.extraction.inter_4588, KeccakfPermAir.extraction.inter_4587, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4586 c row = (mc 1480 + mc 1903 - mc 1561*mc 1903 - 2*mc 1480*mc 1903 + 2*mc 1480*mc 1561*mc 1903) + 2 * KeccakfPermAir.extraction.inter_4584 c row := by
    simp only [KeccakfPermAir.extraction.inter_4586, KeccakfPermAir.extraction.inter_4585, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4584 c row = (mc 1481 + mc 1904 - mc 1562*mc 1904 - 2*mc 1481*mc 1904 + 2*mc 1481*mc 1562*mc 1904) + 2 * KeccakfPermAir.extraction.inter_4582 c row := by
    simp only [KeccakfPermAir.extraction.inter_4584, KeccakfPermAir.extraction.inter_4583, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4582 c row = (mc 1482 + mc 1905 - mc 1563*mc 1905 - 2*mc 1482*mc 1905 + 2*mc 1482*mc 1563*mc 1905) + 2 * KeccakfPermAir.extraction.inter_4580 c row := by
    simp only [KeccakfPermAir.extraction.inter_4582, KeccakfPermAir.extraction.inter_4581, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4580 c row = (mc 1483 + mc 1906 - mc 1564*mc 1906 - 2*mc 1483*mc 1906 + 2*mc 1483*mc 1564*mc 1906) + 2 * KeccakfPermAir.extraction.inter_4578 c row := by
    simp only [KeccakfPermAir.extraction.inter_4580, KeccakfPermAir.extraction.inter_4579, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4578 c row = (mc 1484 + mc 1907 - mc 1565*mc 1907 - 2*mc 1484*mc 1907 + 2*mc 1484*mc 1565*mc 1907) := by
    simp only [KeccakfPermAir.extraction.inter_4578, KeccakfPermAir.extraction.inter_4577, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2938 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2938 c row) :
    ((mc 1566 + mc 2276 - mc 1908*mc 2276 - 2*mc 1566*mc 2276 + 2*mc 1566*mc 1908*mc 2276) + 2*(mc 1567 + mc 2277 - mc 1909*mc 2277 - 2*mc 1567*mc 2277 + 2*mc 1567*mc 1909*mc 2277) + 4*(mc 1568 + mc 2278 - mc 1910*mc 2278 - 2*mc 1568*mc 2278 + 2*mc 1568*mc 1910*mc 2278) + 8*(mc 1505 + mc 2279 - mc 1911*mc 2279 - 2*mc 1505*mc 2279 + 2*mc 1505*mc 1911*mc 2279) + 16*(mc 1506 + mc 2280 - mc 1912*mc 2280 - 2*mc 1506*mc 2280 + 2*mc 1506*mc 1912*mc 2280) + 32*(mc 1507 + mc 2281 - mc 1913*mc 2281 - 2*mc 1507*mc 2281 + 2*mc 1507*mc 1913*mc 2281) + 64*(mc 1508 + mc 2282 - mc 1914*mc 2282 - 2*mc 1508*mc 2282 + 2*mc 1508*mc 1914*mc 2282) + 128*(mc 1509 + mc 2283 - mc 1915*mc 2283 - 2*mc 1509*mc 2283 + 2*mc 1509*mc 1915*mc 2283) + 256*(mc 1510 + mc 2284 - mc 1916*mc 2284 - 2*mc 1510*mc 2284 + 2*mc 1510*mc 1916*mc 2284) + 512*(mc 1511 + mc 2285 - mc 1917*mc 2285 - 2*mc 1511*mc 2285 + 2*mc 1511*mc 1917*mc 2285) + 1024*(mc 1512 + mc 2286 - mc 1918*mc 2286 - 2*mc 1512*mc 2286 + 2*mc 1512*mc 1918*mc 2286) + 2048*(mc 1513 + mc 2287 - mc 1919*mc 2287 - 2*mc 1513*mc 2287 + 2*mc 1513*mc 1919*mc 2287) + 4096*(mc 1514 + mc 2288 - mc 1920*mc 2288 - 2*mc 1514*mc 2288 + 2*mc 1514*mc 1920*mc 2288) + 8192*(mc 1515 + mc 2289 - mc 1921*mc 2289 - 2*mc 1515*mc 2289 + 2*mc 1515*mc 1921*mc 2289) + 16384*(mc 1516 + mc 2290 - mc 1922*mc 2290 - 2*mc 1516*mc 2290 + 2*mc 1516*mc 1922*mc 2290) + 32768*(mc 1517 + mc 2291 - mc 1923*mc 2291 - 2*mc 1517*mc 2291 + 2*mc 1517*mc 1923*mc 2291)) - mc 2493 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2938, KeccakfPermAir.extraction.inter_4638, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4637 c row = (mc 1567 + mc 2277 - mc 1909*mc 2277 - 2*mc 1567*mc 2277 + 2*mc 1567*mc 1909*mc 2277) + 2 * KeccakfPermAir.extraction.inter_4635 c row := by
    simp only [KeccakfPermAir.extraction.inter_4637, KeccakfPermAir.extraction.inter_4636, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4635 c row = (mc 1568 + mc 2278 - mc 1910*mc 2278 - 2*mc 1568*mc 2278 + 2*mc 1568*mc 1910*mc 2278) + 2 * KeccakfPermAir.extraction.inter_4633 c row := by
    simp only [KeccakfPermAir.extraction.inter_4635, KeccakfPermAir.extraction.inter_4634, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4633 c row = (mc 1505 + mc 2279 - mc 1911*mc 2279 - 2*mc 1505*mc 2279 + 2*mc 1505*mc 1911*mc 2279) + 2 * KeccakfPermAir.extraction.inter_4631 c row := by
    simp only [KeccakfPermAir.extraction.inter_4633, KeccakfPermAir.extraction.inter_4632, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4631 c row = (mc 1506 + mc 2280 - mc 1912*mc 2280 - 2*mc 1506*mc 2280 + 2*mc 1506*mc 1912*mc 2280) + 2 * KeccakfPermAir.extraction.inter_4629 c row := by
    simp only [KeccakfPermAir.extraction.inter_4631, KeccakfPermAir.extraction.inter_4630, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4629 c row = (mc 1507 + mc 2281 - mc 1913*mc 2281 - 2*mc 1507*mc 2281 + 2*mc 1507*mc 1913*mc 2281) + 2 * KeccakfPermAir.extraction.inter_4627 c row := by
    simp only [KeccakfPermAir.extraction.inter_4629, KeccakfPermAir.extraction.inter_4628, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4627 c row = (mc 1508 + mc 2282 - mc 1914*mc 2282 - 2*mc 1508*mc 2282 + 2*mc 1508*mc 1914*mc 2282) + 2 * KeccakfPermAir.extraction.inter_4625 c row := by
    simp only [KeccakfPermAir.extraction.inter_4627, KeccakfPermAir.extraction.inter_4626, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4625 c row = (mc 1509 + mc 2283 - mc 1915*mc 2283 - 2*mc 1509*mc 2283 + 2*mc 1509*mc 1915*mc 2283) + 2 * KeccakfPermAir.extraction.inter_4623 c row := by
    simp only [KeccakfPermAir.extraction.inter_4625, KeccakfPermAir.extraction.inter_4624, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4623 c row = (mc 1510 + mc 2284 - mc 1916*mc 2284 - 2*mc 1510*mc 2284 + 2*mc 1510*mc 1916*mc 2284) + 2 * KeccakfPermAir.extraction.inter_4621 c row := by
    simp only [KeccakfPermAir.extraction.inter_4623, KeccakfPermAir.extraction.inter_4622, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4621 c row = (mc 1511 + mc 2285 - mc 1917*mc 2285 - 2*mc 1511*mc 2285 + 2*mc 1511*mc 1917*mc 2285) + 2 * KeccakfPermAir.extraction.inter_4619 c row := by
    simp only [KeccakfPermAir.extraction.inter_4621, KeccakfPermAir.extraction.inter_4620, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4619 c row = (mc 1512 + mc 2286 - mc 1918*mc 2286 - 2*mc 1512*mc 2286 + 2*mc 1512*mc 1918*mc 2286) + 2 * KeccakfPermAir.extraction.inter_4617 c row := by
    simp only [KeccakfPermAir.extraction.inter_4619, KeccakfPermAir.extraction.inter_4618, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4617 c row = (mc 1513 + mc 2287 - mc 1919*mc 2287 - 2*mc 1513*mc 2287 + 2*mc 1513*mc 1919*mc 2287) + 2 * KeccakfPermAir.extraction.inter_4615 c row := by
    simp only [KeccakfPermAir.extraction.inter_4617, KeccakfPermAir.extraction.inter_4616, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4615 c row = (mc 1514 + mc 2288 - mc 1920*mc 2288 - 2*mc 1514*mc 2288 + 2*mc 1514*mc 1920*mc 2288) + 2 * KeccakfPermAir.extraction.inter_4613 c row := by
    simp only [KeccakfPermAir.extraction.inter_4615, KeccakfPermAir.extraction.inter_4614, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4613 c row = (mc 1515 + mc 2289 - mc 1921*mc 2289 - 2*mc 1515*mc 2289 + 2*mc 1515*mc 1921*mc 2289) + 2 * KeccakfPermAir.extraction.inter_4611 c row := by
    simp only [KeccakfPermAir.extraction.inter_4613, KeccakfPermAir.extraction.inter_4612, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4611 c row = (mc 1516 + mc 2290 - mc 1922*mc 2290 - 2*mc 1516*mc 2290 + 2*mc 1516*mc 1922*mc 2290) + 2 * KeccakfPermAir.extraction.inter_4609 c row := by
    simp only [KeccakfPermAir.extraction.inter_4611, KeccakfPermAir.extraction.inter_4610, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4609 c row = (mc 1517 + mc 2291 - mc 1923*mc 2291 - 2*mc 1517*mc 2291 + 2*mc 1517*mc 1923*mc 2291) := by
    simp only [KeccakfPermAir.extraction.inter_4609, KeccakfPermAir.extraction.inter_4608, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2939 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2939 c row) :
    ((mc 1518 + mc 2292 - mc 1924*mc 2292 - 2*mc 1518*mc 2292 + 2*mc 1518*mc 1924*mc 2292) + 2*(mc 1519 + mc 2293 - mc 1925*mc 2293 - 2*mc 1519*mc 2293 + 2*mc 1519*mc 1925*mc 2293) + 4*(mc 1520 + mc 2294 - mc 1926*mc 2294 - 2*mc 1520*mc 2294 + 2*mc 1520*mc 1926*mc 2294) + 8*(mc 1521 + mc 2295 - mc 1927*mc 2295 - 2*mc 1521*mc 2295 + 2*mc 1521*mc 1927*mc 2295) + 16*(mc 1522 + mc 2296 - mc 1928*mc 2296 - 2*mc 1522*mc 2296 + 2*mc 1522*mc 1928*mc 2296) + 32*(mc 1523 + mc 2297 - mc 1929*mc 2297 - 2*mc 1523*mc 2297 + 2*mc 1523*mc 1929*mc 2297) + 64*(mc 1524 + mc 2298 - mc 1930*mc 2298 - 2*mc 1524*mc 2298 + 2*mc 1524*mc 1930*mc 2298) + 128*(mc 1525 + mc 2299 - mc 1931*mc 2299 - 2*mc 1525*mc 2299 + 2*mc 1525*mc 1931*mc 2299) + 256*(mc 1526 + mc 2300 - mc 1932*mc 2300 - 2*mc 1526*mc 2300 + 2*mc 1526*mc 1932*mc 2300) + 512*(mc 1527 + mc 2301 - mc 1933*mc 2301 - 2*mc 1527*mc 2301 + 2*mc 1527*mc 1933*mc 2301) + 1024*(mc 1528 + mc 2302 - mc 1934*mc 2302 - 2*mc 1528*mc 2302 + 2*mc 1528*mc 1934*mc 2302) + 2048*(mc 1529 + mc 2303 - mc 1935*mc 2303 - 2*mc 1529*mc 2303 + 2*mc 1529*mc 1935*mc 2303) + 4096*(mc 1530 + mc 2304 - mc 1936*mc 2304 - 2*mc 1530*mc 2304 + 2*mc 1530*mc 1936*mc 2304) + 8192*(mc 1531 + mc 2305 - mc 1937*mc 2305 - 2*mc 1531*mc 2305 + 2*mc 1531*mc 1937*mc 2305) + 16384*(mc 1532 + mc 2306 - mc 1938*mc 2306 - 2*mc 1532*mc 2306 + 2*mc 1532*mc 1938*mc 2306) + 32768*(mc 1533 + mc 2307 - mc 1939*mc 2307 - 2*mc 1533*mc 2307 + 2*mc 1533*mc 1939*mc 2307)) - mc 2494 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2939, KeccakfPermAir.extraction.inter_4669, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4668 c row = (mc 1519 + mc 2293 - mc 1925*mc 2293 - 2*mc 1519*mc 2293 + 2*mc 1519*mc 1925*mc 2293) + 2 * KeccakfPermAir.extraction.inter_4666 c row := by
    simp only [KeccakfPermAir.extraction.inter_4668, KeccakfPermAir.extraction.inter_4667, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4666 c row = (mc 1520 + mc 2294 - mc 1926*mc 2294 - 2*mc 1520*mc 2294 + 2*mc 1520*mc 1926*mc 2294) + 2 * KeccakfPermAir.extraction.inter_4664 c row := by
    simp only [KeccakfPermAir.extraction.inter_4666, KeccakfPermAir.extraction.inter_4665, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4664 c row = (mc 1521 + mc 2295 - mc 1927*mc 2295 - 2*mc 1521*mc 2295 + 2*mc 1521*mc 1927*mc 2295) + 2 * KeccakfPermAir.extraction.inter_4662 c row := by
    simp only [KeccakfPermAir.extraction.inter_4664, KeccakfPermAir.extraction.inter_4663, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4662 c row = (mc 1522 + mc 2296 - mc 1928*mc 2296 - 2*mc 1522*mc 2296 + 2*mc 1522*mc 1928*mc 2296) + 2 * KeccakfPermAir.extraction.inter_4660 c row := by
    simp only [KeccakfPermAir.extraction.inter_4662, KeccakfPermAir.extraction.inter_4661, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4660 c row = (mc 1523 + mc 2297 - mc 1929*mc 2297 - 2*mc 1523*mc 2297 + 2*mc 1523*mc 1929*mc 2297) + 2 * KeccakfPermAir.extraction.inter_4658 c row := by
    simp only [KeccakfPermAir.extraction.inter_4660, KeccakfPermAir.extraction.inter_4659, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4658 c row = (mc 1524 + mc 2298 - mc 1930*mc 2298 - 2*mc 1524*mc 2298 + 2*mc 1524*mc 1930*mc 2298) + 2 * KeccakfPermAir.extraction.inter_4656 c row := by
    simp only [KeccakfPermAir.extraction.inter_4658, KeccakfPermAir.extraction.inter_4657, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4656 c row = (mc 1525 + mc 2299 - mc 1931*mc 2299 - 2*mc 1525*mc 2299 + 2*mc 1525*mc 1931*mc 2299) + 2 * KeccakfPermAir.extraction.inter_4654 c row := by
    simp only [KeccakfPermAir.extraction.inter_4656, KeccakfPermAir.extraction.inter_4655, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4654 c row = (mc 1526 + mc 2300 - mc 1932*mc 2300 - 2*mc 1526*mc 2300 + 2*mc 1526*mc 1932*mc 2300) + 2 * KeccakfPermAir.extraction.inter_4652 c row := by
    simp only [KeccakfPermAir.extraction.inter_4654, KeccakfPermAir.extraction.inter_4653, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4652 c row = (mc 1527 + mc 2301 - mc 1933*mc 2301 - 2*mc 1527*mc 2301 + 2*mc 1527*mc 1933*mc 2301) + 2 * KeccakfPermAir.extraction.inter_4650 c row := by
    simp only [KeccakfPermAir.extraction.inter_4652, KeccakfPermAir.extraction.inter_4651, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4650 c row = (mc 1528 + mc 2302 - mc 1934*mc 2302 - 2*mc 1528*mc 2302 + 2*mc 1528*mc 1934*mc 2302) + 2 * KeccakfPermAir.extraction.inter_4648 c row := by
    simp only [KeccakfPermAir.extraction.inter_4650, KeccakfPermAir.extraction.inter_4649, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4648 c row = (mc 1529 + mc 2303 - mc 1935*mc 2303 - 2*mc 1529*mc 2303 + 2*mc 1529*mc 1935*mc 2303) + 2 * KeccakfPermAir.extraction.inter_4646 c row := by
    simp only [KeccakfPermAir.extraction.inter_4648, KeccakfPermAir.extraction.inter_4647, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4646 c row = (mc 1530 + mc 2304 - mc 1936*mc 2304 - 2*mc 1530*mc 2304 + 2*mc 1530*mc 1936*mc 2304) + 2 * KeccakfPermAir.extraction.inter_4644 c row := by
    simp only [KeccakfPermAir.extraction.inter_4646, KeccakfPermAir.extraction.inter_4645, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4644 c row = (mc 1531 + mc 2305 - mc 1937*mc 2305 - 2*mc 1531*mc 2305 + 2*mc 1531*mc 1937*mc 2305) + 2 * KeccakfPermAir.extraction.inter_4642 c row := by
    simp only [KeccakfPermAir.extraction.inter_4644, KeccakfPermAir.extraction.inter_4643, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4642 c row = (mc 1532 + mc 2306 - mc 1938*mc 2306 - 2*mc 1532*mc 2306 + 2*mc 1532*mc 1938*mc 2306) + 2 * KeccakfPermAir.extraction.inter_4640 c row := by
    simp only [KeccakfPermAir.extraction.inter_4642, KeccakfPermAir.extraction.inter_4641, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4640 c row = (mc 1533 + mc 2307 - mc 1939*mc 2307 - 2*mc 1533*mc 2307 + 2*mc 1533*mc 1939*mc 2307) := by
    simp only [KeccakfPermAir.extraction.inter_4640, KeccakfPermAir.extraction.inter_4639, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2940 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2940 c row) :
    ((mc 1534 + mc 2308 - mc 1940*mc 2308 - 2*mc 1534*mc 2308 + 2*mc 1534*mc 1940*mc 2308) + 2*(mc 1535 + mc 2309 - mc 1941*mc 2309 - 2*mc 1535*mc 2309 + 2*mc 1535*mc 1941*mc 2309) + 4*(mc 1536 + mc 2310 - mc 1942*mc 2310 - 2*mc 1536*mc 2310 + 2*mc 1536*mc 1942*mc 2310) + 8*(mc 1537 + mc 2311 - mc 1943*mc 2311 - 2*mc 1537*mc 2311 + 2*mc 1537*mc 1943*mc 2311) + 16*(mc 1538 + mc 2312 - mc 1944*mc 2312 - 2*mc 1538*mc 2312 + 2*mc 1538*mc 1944*mc 2312) + 32*(mc 1539 + mc 2313 - mc 1945*mc 2313 - 2*mc 1539*mc 2313 + 2*mc 1539*mc 1945*mc 2313) + 64*(mc 1540 + mc 2314 - mc 1946*mc 2314 - 2*mc 1540*mc 2314 + 2*mc 1540*mc 1946*mc 2314) + 128*(mc 1541 + mc 2315 - mc 1947*mc 2315 - 2*mc 1541*mc 2315 + 2*mc 1541*mc 1947*mc 2315) + 256*(mc 1542 + mc 2316 - mc 1948*mc 2316 - 2*mc 1542*mc 2316 + 2*mc 1542*mc 1948*mc 2316) + 512*(mc 1543 + mc 2317 - mc 1949*mc 2317 - 2*mc 1543*mc 2317 + 2*mc 1543*mc 1949*mc 2317) + 1024*(mc 1544 + mc 2318 - mc 1950*mc 2318 - 2*mc 1544*mc 2318 + 2*mc 1544*mc 1950*mc 2318) + 2048*(mc 1545 + mc 2319 - mc 1951*mc 2319 - 2*mc 1545*mc 2319 + 2*mc 1545*mc 1951*mc 2319) + 4096*(mc 1546 + mc 2320 - mc 1952*mc 2320 - 2*mc 1546*mc 2320 + 2*mc 1546*mc 1952*mc 2320) + 8192*(mc 1547 + mc 2321 - mc 1889*mc 2321 - 2*mc 1547*mc 2321 + 2*mc 1547*mc 1889*mc 2321) + 16384*(mc 1548 + mc 2322 - mc 1890*mc 2322 - 2*mc 1548*mc 2322 + 2*mc 1548*mc 1890*mc 2322) + 32768*(mc 1549 + mc 2323 - mc 1891*mc 2323 - 2*mc 1549*mc 2323 + 2*mc 1549*mc 1891*mc 2323)) - mc 2495 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2940, KeccakfPermAir.extraction.inter_4700, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4699 c row = (mc 1535 + mc 2309 - mc 1941*mc 2309 - 2*mc 1535*mc 2309 + 2*mc 1535*mc 1941*mc 2309) + 2 * KeccakfPermAir.extraction.inter_4697 c row := by
    simp only [KeccakfPermAir.extraction.inter_4699, KeccakfPermAir.extraction.inter_4698, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4697 c row = (mc 1536 + mc 2310 - mc 1942*mc 2310 - 2*mc 1536*mc 2310 + 2*mc 1536*mc 1942*mc 2310) + 2 * KeccakfPermAir.extraction.inter_4695 c row := by
    simp only [KeccakfPermAir.extraction.inter_4697, KeccakfPermAir.extraction.inter_4696, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4695 c row = (mc 1537 + mc 2311 - mc 1943*mc 2311 - 2*mc 1537*mc 2311 + 2*mc 1537*mc 1943*mc 2311) + 2 * KeccakfPermAir.extraction.inter_4693 c row := by
    simp only [KeccakfPermAir.extraction.inter_4695, KeccakfPermAir.extraction.inter_4694, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4693 c row = (mc 1538 + mc 2312 - mc 1944*mc 2312 - 2*mc 1538*mc 2312 + 2*mc 1538*mc 1944*mc 2312) + 2 * KeccakfPermAir.extraction.inter_4691 c row := by
    simp only [KeccakfPermAir.extraction.inter_4693, KeccakfPermAir.extraction.inter_4692, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4691 c row = (mc 1539 + mc 2313 - mc 1945*mc 2313 - 2*mc 1539*mc 2313 + 2*mc 1539*mc 1945*mc 2313) + 2 * KeccakfPermAir.extraction.inter_4689 c row := by
    simp only [KeccakfPermAir.extraction.inter_4691, KeccakfPermAir.extraction.inter_4690, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4689 c row = (mc 1540 + mc 2314 - mc 1946*mc 2314 - 2*mc 1540*mc 2314 + 2*mc 1540*mc 1946*mc 2314) + 2 * KeccakfPermAir.extraction.inter_4687 c row := by
    simp only [KeccakfPermAir.extraction.inter_4689, KeccakfPermAir.extraction.inter_4688, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4687 c row = (mc 1541 + mc 2315 - mc 1947*mc 2315 - 2*mc 1541*mc 2315 + 2*mc 1541*mc 1947*mc 2315) + 2 * KeccakfPermAir.extraction.inter_4685 c row := by
    simp only [KeccakfPermAir.extraction.inter_4687, KeccakfPermAir.extraction.inter_4686, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4685 c row = (mc 1542 + mc 2316 - mc 1948*mc 2316 - 2*mc 1542*mc 2316 + 2*mc 1542*mc 1948*mc 2316) + 2 * KeccakfPermAir.extraction.inter_4683 c row := by
    simp only [KeccakfPermAir.extraction.inter_4685, KeccakfPermAir.extraction.inter_4684, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4683 c row = (mc 1543 + mc 2317 - mc 1949*mc 2317 - 2*mc 1543*mc 2317 + 2*mc 1543*mc 1949*mc 2317) + 2 * KeccakfPermAir.extraction.inter_4681 c row := by
    simp only [KeccakfPermAir.extraction.inter_4683, KeccakfPermAir.extraction.inter_4682, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4681 c row = (mc 1544 + mc 2318 - mc 1950*mc 2318 - 2*mc 1544*mc 2318 + 2*mc 1544*mc 1950*mc 2318) + 2 * KeccakfPermAir.extraction.inter_4679 c row := by
    simp only [KeccakfPermAir.extraction.inter_4681, KeccakfPermAir.extraction.inter_4680, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4679 c row = (mc 1545 + mc 2319 - mc 1951*mc 2319 - 2*mc 1545*mc 2319 + 2*mc 1545*mc 1951*mc 2319) + 2 * KeccakfPermAir.extraction.inter_4677 c row := by
    simp only [KeccakfPermAir.extraction.inter_4679, KeccakfPermAir.extraction.inter_4678, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4677 c row = (mc 1546 + mc 2320 - mc 1952*mc 2320 - 2*mc 1546*mc 2320 + 2*mc 1546*mc 1952*mc 2320) + 2 * KeccakfPermAir.extraction.inter_4675 c row := by
    simp only [KeccakfPermAir.extraction.inter_4677, KeccakfPermAir.extraction.inter_4676, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4675 c row = (mc 1547 + mc 2321 - mc 1889*mc 2321 - 2*mc 1547*mc 2321 + 2*mc 1547*mc 1889*mc 2321) + 2 * KeccakfPermAir.extraction.inter_4673 c row := by
    simp only [KeccakfPermAir.extraction.inter_4675, KeccakfPermAir.extraction.inter_4674, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4673 c row = (mc 1548 + mc 2322 - mc 1890*mc 2322 - 2*mc 1548*mc 2322 + 2*mc 1548*mc 1890*mc 2322) + 2 * KeccakfPermAir.extraction.inter_4671 c row := by
    simp only [KeccakfPermAir.extraction.inter_4673, KeccakfPermAir.extraction.inter_4672, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4671 c row = (mc 1549 + mc 2323 - mc 1891*mc 2323 - 2*mc 1549*mc 2323 + 2*mc 1549*mc 1891*mc 2323) := by
    simp only [KeccakfPermAir.extraction.inter_4671, KeccakfPermAir.extraction.inter_4670, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2941 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2941 c row) :
    ((mc 1550 + mc 2324 - mc 1892*mc 2324 - 2*mc 1550*mc 2324 + 2*mc 1550*mc 1892*mc 2324) + 2*(mc 1551 + mc 2325 - mc 1893*mc 2325 - 2*mc 1551*mc 2325 + 2*mc 1551*mc 1893*mc 2325) + 4*(mc 1552 + mc 2326 - mc 1894*mc 2326 - 2*mc 1552*mc 2326 + 2*mc 1552*mc 1894*mc 2326) + 8*(mc 1553 + mc 2327 - mc 1895*mc 2327 - 2*mc 1553*mc 2327 + 2*mc 1553*mc 1895*mc 2327) + 16*(mc 1554 + mc 2328 - mc 1896*mc 2328 - 2*mc 1554*mc 2328 + 2*mc 1554*mc 1896*mc 2328) + 32*(mc 1555 + mc 2329 - mc 1897*mc 2329 - 2*mc 1555*mc 2329 + 2*mc 1555*mc 1897*mc 2329) + 64*(mc 1556 + mc 2330 - mc 1898*mc 2330 - 2*mc 1556*mc 2330 + 2*mc 1556*mc 1898*mc 2330) + 128*(mc 1557 + mc 2331 - mc 1899*mc 2331 - 2*mc 1557*mc 2331 + 2*mc 1557*mc 1899*mc 2331) + 256*(mc 1558 + mc 2332 - mc 1900*mc 2332 - 2*mc 1558*mc 2332 + 2*mc 1558*mc 1900*mc 2332) + 512*(mc 1559 + mc 2333 - mc 1901*mc 2333 - 2*mc 1559*mc 2333 + 2*mc 1559*mc 1901*mc 2333) + 1024*(mc 1560 + mc 2334 - mc 1902*mc 2334 - 2*mc 1560*mc 2334 + 2*mc 1560*mc 1902*mc 2334) + 2048*(mc 1561 + mc 2335 - mc 1903*mc 2335 - 2*mc 1561*mc 2335 + 2*mc 1561*mc 1903*mc 2335) + 4096*(mc 1562 + mc 2336 - mc 1904*mc 2336 - 2*mc 1562*mc 2336 + 2*mc 1562*mc 1904*mc 2336) + 8192*(mc 1563 + mc 2273 - mc 1905*mc 2273 - 2*mc 1563*mc 2273 + 2*mc 1563*mc 1905*mc 2273) + 16384*(mc 1564 + mc 2274 - mc 1906*mc 2274 - 2*mc 1564*mc 2274 + 2*mc 1564*mc 1906*mc 2274) + 32768*(mc 1565 + mc 2275 - mc 1907*mc 2275 - 2*mc 1565*mc 2275 + 2*mc 1565*mc 1907*mc 2275)) - mc 2496 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2941, KeccakfPermAir.extraction.inter_4731, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4730 c row = (mc 1551 + mc 2325 - mc 1893*mc 2325 - 2*mc 1551*mc 2325 + 2*mc 1551*mc 1893*mc 2325) + 2 * KeccakfPermAir.extraction.inter_4728 c row := by
    simp only [KeccakfPermAir.extraction.inter_4730, KeccakfPermAir.extraction.inter_4729, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4728 c row = (mc 1552 + mc 2326 - mc 1894*mc 2326 - 2*mc 1552*mc 2326 + 2*mc 1552*mc 1894*mc 2326) + 2 * KeccakfPermAir.extraction.inter_4726 c row := by
    simp only [KeccakfPermAir.extraction.inter_4728, KeccakfPermAir.extraction.inter_4727, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4726 c row = (mc 1553 + mc 2327 - mc 1895*mc 2327 - 2*mc 1553*mc 2327 + 2*mc 1553*mc 1895*mc 2327) + 2 * KeccakfPermAir.extraction.inter_4724 c row := by
    simp only [KeccakfPermAir.extraction.inter_4726, KeccakfPermAir.extraction.inter_4725, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4724 c row = (mc 1554 + mc 2328 - mc 1896*mc 2328 - 2*mc 1554*mc 2328 + 2*mc 1554*mc 1896*mc 2328) + 2 * KeccakfPermAir.extraction.inter_4722 c row := by
    simp only [KeccakfPermAir.extraction.inter_4724, KeccakfPermAir.extraction.inter_4723, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4722 c row = (mc 1555 + mc 2329 - mc 1897*mc 2329 - 2*mc 1555*mc 2329 + 2*mc 1555*mc 1897*mc 2329) + 2 * KeccakfPermAir.extraction.inter_4720 c row := by
    simp only [KeccakfPermAir.extraction.inter_4722, KeccakfPermAir.extraction.inter_4721, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4720 c row = (mc 1556 + mc 2330 - mc 1898*mc 2330 - 2*mc 1556*mc 2330 + 2*mc 1556*mc 1898*mc 2330) + 2 * KeccakfPermAir.extraction.inter_4718 c row := by
    simp only [KeccakfPermAir.extraction.inter_4720, KeccakfPermAir.extraction.inter_4719, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4718 c row = (mc 1557 + mc 2331 - mc 1899*mc 2331 - 2*mc 1557*mc 2331 + 2*mc 1557*mc 1899*mc 2331) + 2 * KeccakfPermAir.extraction.inter_4716 c row := by
    simp only [KeccakfPermAir.extraction.inter_4718, KeccakfPermAir.extraction.inter_4717, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4716 c row = (mc 1558 + mc 2332 - mc 1900*mc 2332 - 2*mc 1558*mc 2332 + 2*mc 1558*mc 1900*mc 2332) + 2 * KeccakfPermAir.extraction.inter_4714 c row := by
    simp only [KeccakfPermAir.extraction.inter_4716, KeccakfPermAir.extraction.inter_4715, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4714 c row = (mc 1559 + mc 2333 - mc 1901*mc 2333 - 2*mc 1559*mc 2333 + 2*mc 1559*mc 1901*mc 2333) + 2 * KeccakfPermAir.extraction.inter_4712 c row := by
    simp only [KeccakfPermAir.extraction.inter_4714, KeccakfPermAir.extraction.inter_4713, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4712 c row = (mc 1560 + mc 2334 - mc 1902*mc 2334 - 2*mc 1560*mc 2334 + 2*mc 1560*mc 1902*mc 2334) + 2 * KeccakfPermAir.extraction.inter_4710 c row := by
    simp only [KeccakfPermAir.extraction.inter_4712, KeccakfPermAir.extraction.inter_4711, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4710 c row = (mc 1561 + mc 2335 - mc 1903*mc 2335 - 2*mc 1561*mc 2335 + 2*mc 1561*mc 1903*mc 2335) + 2 * KeccakfPermAir.extraction.inter_4708 c row := by
    simp only [KeccakfPermAir.extraction.inter_4710, KeccakfPermAir.extraction.inter_4709, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4708 c row = (mc 1562 + mc 2336 - mc 1904*mc 2336 - 2*mc 1562*mc 2336 + 2*mc 1562*mc 1904*mc 2336) + 2 * KeccakfPermAir.extraction.inter_4706 c row := by
    simp only [KeccakfPermAir.extraction.inter_4708, KeccakfPermAir.extraction.inter_4707, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4706 c row = (mc 1563 + mc 2273 - mc 1905*mc 2273 - 2*mc 1563*mc 2273 + 2*mc 1563*mc 1905*mc 2273) + 2 * KeccakfPermAir.extraction.inter_4704 c row := by
    simp only [KeccakfPermAir.extraction.inter_4706, KeccakfPermAir.extraction.inter_4705, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4704 c row = (mc 1564 + mc 2274 - mc 1906*mc 2274 - 2*mc 1564*mc 2274 + 2*mc 1564*mc 1906*mc 2274) + 2 * KeccakfPermAir.extraction.inter_4702 c row := by
    simp only [KeccakfPermAir.extraction.inter_4704, KeccakfPermAir.extraction.inter_4703, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4702 c row = (mc 1565 + mc 2275 - mc 1907*mc 2275 - 2*mc 1565*mc 2275 + 2*mc 1565*mc 1907*mc 2275) := by
    simp only [KeccakfPermAir.extraction.inter_4702, KeccakfPermAir.extraction.inter_4701, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2942 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2942 c row) :
    ((mc 1908 + mc 1093 - mc 2276*mc 1093 - 2*mc 1908*mc 1093 + 2*mc 1908*mc 2276*mc 1093) + 2*(mc 1909 + mc 1094 - mc 2277*mc 1094 - 2*mc 1909*mc 1094 + 2*mc 1909*mc 2277*mc 1094) + 4*(mc 1910 + mc 1095 - mc 2278*mc 1095 - 2*mc 1910*mc 1095 + 2*mc 1910*mc 2278*mc 1095) + 8*(mc 1911 + mc 1096 - mc 2279*mc 1096 - 2*mc 1911*mc 1096 + 2*mc 1911*mc 2279*mc 1096) + 16*(mc 1912 + mc 1097 - mc 2280*mc 1097 - 2*mc 1912*mc 1097 + 2*mc 1912*mc 2280*mc 1097) + 32*(mc 1913 + mc 1098 - mc 2281*mc 1098 - 2*mc 1913*mc 1098 + 2*mc 1913*mc 2281*mc 1098) + 64*(mc 1914 + mc 1099 - mc 2282*mc 1099 - 2*mc 1914*mc 1099 + 2*mc 1914*mc 2282*mc 1099) + 128*(mc 1915 + mc 1100 - mc 2283*mc 1100 - 2*mc 1915*mc 1100 + 2*mc 1915*mc 2283*mc 1100) + 256*(mc 1916 + mc 1101 - mc 2284*mc 1101 - 2*mc 1916*mc 1101 + 2*mc 1916*mc 2284*mc 1101) + 512*(mc 1917 + mc 1102 - mc 2285*mc 1102 - 2*mc 1917*mc 1102 + 2*mc 1917*mc 2285*mc 1102) + 1024*(mc 1918 + mc 1103 - mc 2286*mc 1103 - 2*mc 1918*mc 1103 + 2*mc 1918*mc 2286*mc 1103) + 2048*(mc 1919 + mc 1104 - mc 2287*mc 1104 - 2*mc 1919*mc 1104 + 2*mc 1919*mc 2287*mc 1104) + 4096*(mc 1920 + mc 1105 - mc 2288*mc 1105 - 2*mc 1920*mc 1105 + 2*mc 1920*mc 2288*mc 1105) + 8192*(mc 1921 + mc 1106 - mc 2289*mc 1106 - 2*mc 1921*mc 1106 + 2*mc 1921*mc 2289*mc 1106) + 16384*(mc 1922 + mc 1107 - mc 2290*mc 1107 - 2*mc 1922*mc 1107 + 2*mc 1922*mc 2290*mc 1107) + 32768*(mc 1923 + mc 1108 - mc 2291*mc 1108 - 2*mc 1923*mc 1108 + 2*mc 1923*mc 2291*mc 1108)) - mc 2497 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2942, KeccakfPermAir.extraction.inter_4762, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4761 c row = (mc 1909 + mc 1094 - mc 2277*mc 1094 - 2*mc 1909*mc 1094 + 2*mc 1909*mc 2277*mc 1094) + 2 * KeccakfPermAir.extraction.inter_4759 c row := by
    simp only [KeccakfPermAir.extraction.inter_4761, KeccakfPermAir.extraction.inter_4760, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4759 c row = (mc 1910 + mc 1095 - mc 2278*mc 1095 - 2*mc 1910*mc 1095 + 2*mc 1910*mc 2278*mc 1095) + 2 * KeccakfPermAir.extraction.inter_4757 c row := by
    simp only [KeccakfPermAir.extraction.inter_4759, KeccakfPermAir.extraction.inter_4758, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4757 c row = (mc 1911 + mc 1096 - mc 2279*mc 1096 - 2*mc 1911*mc 1096 + 2*mc 1911*mc 2279*mc 1096) + 2 * KeccakfPermAir.extraction.inter_4755 c row := by
    simp only [KeccakfPermAir.extraction.inter_4757, KeccakfPermAir.extraction.inter_4756, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4755 c row = (mc 1912 + mc 1097 - mc 2280*mc 1097 - 2*mc 1912*mc 1097 + 2*mc 1912*mc 2280*mc 1097) + 2 * KeccakfPermAir.extraction.inter_4753 c row := by
    simp only [KeccakfPermAir.extraction.inter_4755, KeccakfPermAir.extraction.inter_4754, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4753 c row = (mc 1913 + mc 1098 - mc 2281*mc 1098 - 2*mc 1913*mc 1098 + 2*mc 1913*mc 2281*mc 1098) + 2 * KeccakfPermAir.extraction.inter_4751 c row := by
    simp only [KeccakfPermAir.extraction.inter_4753, KeccakfPermAir.extraction.inter_4752, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4751 c row = (mc 1914 + mc 1099 - mc 2282*mc 1099 - 2*mc 1914*mc 1099 + 2*mc 1914*mc 2282*mc 1099) + 2 * KeccakfPermAir.extraction.inter_4749 c row := by
    simp only [KeccakfPermAir.extraction.inter_4751, KeccakfPermAir.extraction.inter_4750, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4749 c row = (mc 1915 + mc 1100 - mc 2283*mc 1100 - 2*mc 1915*mc 1100 + 2*mc 1915*mc 2283*mc 1100) + 2 * KeccakfPermAir.extraction.inter_4747 c row := by
    simp only [KeccakfPermAir.extraction.inter_4749, KeccakfPermAir.extraction.inter_4748, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4747 c row = (mc 1916 + mc 1101 - mc 2284*mc 1101 - 2*mc 1916*mc 1101 + 2*mc 1916*mc 2284*mc 1101) + 2 * KeccakfPermAir.extraction.inter_4745 c row := by
    simp only [KeccakfPermAir.extraction.inter_4747, KeccakfPermAir.extraction.inter_4746, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4745 c row = (mc 1917 + mc 1102 - mc 2285*mc 1102 - 2*mc 1917*mc 1102 + 2*mc 1917*mc 2285*mc 1102) + 2 * KeccakfPermAir.extraction.inter_4743 c row := by
    simp only [KeccakfPermAir.extraction.inter_4745, KeccakfPermAir.extraction.inter_4744, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4743 c row = (mc 1918 + mc 1103 - mc 2286*mc 1103 - 2*mc 1918*mc 1103 + 2*mc 1918*mc 2286*mc 1103) + 2 * KeccakfPermAir.extraction.inter_4741 c row := by
    simp only [KeccakfPermAir.extraction.inter_4743, KeccakfPermAir.extraction.inter_4742, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4741 c row = (mc 1919 + mc 1104 - mc 2287*mc 1104 - 2*mc 1919*mc 1104 + 2*mc 1919*mc 2287*mc 1104) + 2 * KeccakfPermAir.extraction.inter_4739 c row := by
    simp only [KeccakfPermAir.extraction.inter_4741, KeccakfPermAir.extraction.inter_4740, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4739 c row = (mc 1920 + mc 1105 - mc 2288*mc 1105 - 2*mc 1920*mc 1105 + 2*mc 1920*mc 2288*mc 1105) + 2 * KeccakfPermAir.extraction.inter_4737 c row := by
    simp only [KeccakfPermAir.extraction.inter_4739, KeccakfPermAir.extraction.inter_4738, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4737 c row = (mc 1921 + mc 1106 - mc 2289*mc 1106 - 2*mc 1921*mc 1106 + 2*mc 1921*mc 2289*mc 1106) + 2 * KeccakfPermAir.extraction.inter_4735 c row := by
    simp only [KeccakfPermAir.extraction.inter_4737, KeccakfPermAir.extraction.inter_4736, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4735 c row = (mc 1922 + mc 1107 - mc 2290*mc 1107 - 2*mc 1922*mc 1107 + 2*mc 1922*mc 2290*mc 1107) + 2 * KeccakfPermAir.extraction.inter_4733 c row := by
    simp only [KeccakfPermAir.extraction.inter_4735, KeccakfPermAir.extraction.inter_4734, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4733 c row = (mc 1923 + mc 1108 - mc 2291*mc 1108 - 2*mc 1923*mc 1108 + 2*mc 1923*mc 2291*mc 1108) := by
    simp only [KeccakfPermAir.extraction.inter_4733, KeccakfPermAir.extraction.inter_4732, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2943 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2943 c row) :
    ((mc 1924 + mc 1109 - mc 2292*mc 1109 - 2*mc 1924*mc 1109 + 2*mc 1924*mc 2292*mc 1109) + 2*(mc 1925 + mc 1110 - mc 2293*mc 1110 - 2*mc 1925*mc 1110 + 2*mc 1925*mc 2293*mc 1110) + 4*(mc 1926 + mc 1111 - mc 2294*mc 1111 - 2*mc 1926*mc 1111 + 2*mc 1926*mc 2294*mc 1111) + 8*(mc 1927 + mc 1112 - mc 2295*mc 1112 - 2*mc 1927*mc 1112 + 2*mc 1927*mc 2295*mc 1112) + 16*(mc 1928 + mc 1113 - mc 2296*mc 1113 - 2*mc 1928*mc 1113 + 2*mc 1928*mc 2296*mc 1113) + 32*(mc 1929 + mc 1114 - mc 2297*mc 1114 - 2*mc 1929*mc 1114 + 2*mc 1929*mc 2297*mc 1114) + 64*(mc 1930 + mc 1115 - mc 2298*mc 1115 - 2*mc 1930*mc 1115 + 2*mc 1930*mc 2298*mc 1115) + 128*(mc 1931 + mc 1116 - mc 2299*mc 1116 - 2*mc 1931*mc 1116 + 2*mc 1931*mc 2299*mc 1116) + 256*(mc 1932 + mc 1117 - mc 2300*mc 1117 - 2*mc 1932*mc 1117 + 2*mc 1932*mc 2300*mc 1117) + 512*(mc 1933 + mc 1118 - mc 2301*mc 1118 - 2*mc 1933*mc 1118 + 2*mc 1933*mc 2301*mc 1118) + 1024*(mc 1934 + mc 1119 - mc 2302*mc 1119 - 2*mc 1934*mc 1119 + 2*mc 1934*mc 2302*mc 1119) + 2048*(mc 1935 + mc 1120 - mc 2303*mc 1120 - 2*mc 1935*mc 1120 + 2*mc 1935*mc 2303*mc 1120) + 4096*(mc 1936 + mc 1057 - mc 2304*mc 1057 - 2*mc 1936*mc 1057 + 2*mc 1936*mc 2304*mc 1057) + 8192*(mc 1937 + mc 1058 - mc 2305*mc 1058 - 2*mc 1937*mc 1058 + 2*mc 1937*mc 2305*mc 1058) + 16384*(mc 1938 + mc 1059 - mc 2306*mc 1059 - 2*mc 1938*mc 1059 + 2*mc 1938*mc 2306*mc 1059) + 32768*(mc 1939 + mc 1060 - mc 2307*mc 1060 - 2*mc 1939*mc 1060 + 2*mc 1939*mc 2307*mc 1060)) - mc 2498 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2943, KeccakfPermAir.extraction.inter_4793, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4792 c row = (mc 1925 + mc 1110 - mc 2293*mc 1110 - 2*mc 1925*mc 1110 + 2*mc 1925*mc 2293*mc 1110) + 2 * KeccakfPermAir.extraction.inter_4790 c row := by
    simp only [KeccakfPermAir.extraction.inter_4792, KeccakfPermAir.extraction.inter_4791, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4790 c row = (mc 1926 + mc 1111 - mc 2294*mc 1111 - 2*mc 1926*mc 1111 + 2*mc 1926*mc 2294*mc 1111) + 2 * KeccakfPermAir.extraction.inter_4788 c row := by
    simp only [KeccakfPermAir.extraction.inter_4790, KeccakfPermAir.extraction.inter_4789, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4788 c row = (mc 1927 + mc 1112 - mc 2295*mc 1112 - 2*mc 1927*mc 1112 + 2*mc 1927*mc 2295*mc 1112) + 2 * KeccakfPermAir.extraction.inter_4786 c row := by
    simp only [KeccakfPermAir.extraction.inter_4788, KeccakfPermAir.extraction.inter_4787, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4786 c row = (mc 1928 + mc 1113 - mc 2296*mc 1113 - 2*mc 1928*mc 1113 + 2*mc 1928*mc 2296*mc 1113) + 2 * KeccakfPermAir.extraction.inter_4784 c row := by
    simp only [KeccakfPermAir.extraction.inter_4786, KeccakfPermAir.extraction.inter_4785, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4784 c row = (mc 1929 + mc 1114 - mc 2297*mc 1114 - 2*mc 1929*mc 1114 + 2*mc 1929*mc 2297*mc 1114) + 2 * KeccakfPermAir.extraction.inter_4782 c row := by
    simp only [KeccakfPermAir.extraction.inter_4784, KeccakfPermAir.extraction.inter_4783, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4782 c row = (mc 1930 + mc 1115 - mc 2298*mc 1115 - 2*mc 1930*mc 1115 + 2*mc 1930*mc 2298*mc 1115) + 2 * KeccakfPermAir.extraction.inter_4780 c row := by
    simp only [KeccakfPermAir.extraction.inter_4782, KeccakfPermAir.extraction.inter_4781, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4780 c row = (mc 1931 + mc 1116 - mc 2299*mc 1116 - 2*mc 1931*mc 1116 + 2*mc 1931*mc 2299*mc 1116) + 2 * KeccakfPermAir.extraction.inter_4778 c row := by
    simp only [KeccakfPermAir.extraction.inter_4780, KeccakfPermAir.extraction.inter_4779, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4778 c row = (mc 1932 + mc 1117 - mc 2300*mc 1117 - 2*mc 1932*mc 1117 + 2*mc 1932*mc 2300*mc 1117) + 2 * KeccakfPermAir.extraction.inter_4776 c row := by
    simp only [KeccakfPermAir.extraction.inter_4778, KeccakfPermAir.extraction.inter_4777, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4776 c row = (mc 1933 + mc 1118 - mc 2301*mc 1118 - 2*mc 1933*mc 1118 + 2*mc 1933*mc 2301*mc 1118) + 2 * KeccakfPermAir.extraction.inter_4774 c row := by
    simp only [KeccakfPermAir.extraction.inter_4776, KeccakfPermAir.extraction.inter_4775, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4774 c row = (mc 1934 + mc 1119 - mc 2302*mc 1119 - 2*mc 1934*mc 1119 + 2*mc 1934*mc 2302*mc 1119) + 2 * KeccakfPermAir.extraction.inter_4772 c row := by
    simp only [KeccakfPermAir.extraction.inter_4774, KeccakfPermAir.extraction.inter_4773, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4772 c row = (mc 1935 + mc 1120 - mc 2303*mc 1120 - 2*mc 1935*mc 1120 + 2*mc 1935*mc 2303*mc 1120) + 2 * KeccakfPermAir.extraction.inter_4770 c row := by
    simp only [KeccakfPermAir.extraction.inter_4772, KeccakfPermAir.extraction.inter_4771, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4770 c row = (mc 1936 + mc 1057 - mc 2304*mc 1057 - 2*mc 1936*mc 1057 + 2*mc 1936*mc 2304*mc 1057) + 2 * KeccakfPermAir.extraction.inter_4768 c row := by
    simp only [KeccakfPermAir.extraction.inter_4770, KeccakfPermAir.extraction.inter_4769, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4768 c row = (mc 1937 + mc 1058 - mc 2305*mc 1058 - 2*mc 1937*mc 1058 + 2*mc 1937*mc 2305*mc 1058) + 2 * KeccakfPermAir.extraction.inter_4766 c row := by
    simp only [KeccakfPermAir.extraction.inter_4768, KeccakfPermAir.extraction.inter_4767, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4766 c row = (mc 1938 + mc 1059 - mc 2306*mc 1059 - 2*mc 1938*mc 1059 + 2*mc 1938*mc 2306*mc 1059) + 2 * KeccakfPermAir.extraction.inter_4764 c row := by
    simp only [KeccakfPermAir.extraction.inter_4766, KeccakfPermAir.extraction.inter_4765, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4764 c row = (mc 1939 + mc 1060 - mc 2307*mc 1060 - 2*mc 1939*mc 1060 + 2*mc 1939*mc 2307*mc 1060) := by
    simp only [KeccakfPermAir.extraction.inter_4764, KeccakfPermAir.extraction.inter_4763, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2944 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2944 c row) :
    ((mc 1940 + mc 1061 - mc 2308*mc 1061 - 2*mc 1940*mc 1061 + 2*mc 1940*mc 2308*mc 1061) + 2*(mc 1941 + mc 1062 - mc 2309*mc 1062 - 2*mc 1941*mc 1062 + 2*mc 1941*mc 2309*mc 1062) + 4*(mc 1942 + mc 1063 - mc 2310*mc 1063 - 2*mc 1942*mc 1063 + 2*mc 1942*mc 2310*mc 1063) + 8*(mc 1943 + mc 1064 - mc 2311*mc 1064 - 2*mc 1943*mc 1064 + 2*mc 1943*mc 2311*mc 1064) + 16*(mc 1944 + mc 1065 - mc 2312*mc 1065 - 2*mc 1944*mc 1065 + 2*mc 1944*mc 2312*mc 1065) + 32*(mc 1945 + mc 1066 - mc 2313*mc 1066 - 2*mc 1945*mc 1066 + 2*mc 1945*mc 2313*mc 1066) + 64*(mc 1946 + mc 1067 - mc 2314*mc 1067 - 2*mc 1946*mc 1067 + 2*mc 1946*mc 2314*mc 1067) + 128*(mc 1947 + mc 1068 - mc 2315*mc 1068 - 2*mc 1947*mc 1068 + 2*mc 1947*mc 2315*mc 1068) + 256*(mc 1948 + mc 1069 - mc 2316*mc 1069 - 2*mc 1948*mc 1069 + 2*mc 1948*mc 2316*mc 1069) + 512*(mc 1949 + mc 1070 - mc 2317*mc 1070 - 2*mc 1949*mc 1070 + 2*mc 1949*mc 2317*mc 1070) + 1024*(mc 1950 + mc 1071 - mc 2318*mc 1071 - 2*mc 1950*mc 1071 + 2*mc 1950*mc 2318*mc 1071) + 2048*(mc 1951 + mc 1072 - mc 2319*mc 1072 - 2*mc 1951*mc 1072 + 2*mc 1951*mc 2319*mc 1072) + 4096*(mc 1952 + mc 1073 - mc 2320*mc 1073 - 2*mc 1952*mc 1073 + 2*mc 1952*mc 2320*mc 1073) + 8192*(mc 1889 + mc 1074 - mc 2321*mc 1074 - 2*mc 1889*mc 1074 + 2*mc 1889*mc 2321*mc 1074) + 16384*(mc 1890 + mc 1075 - mc 2322*mc 1075 - 2*mc 1890*mc 1075 + 2*mc 1890*mc 2322*mc 1075) + 32768*(mc 1891 + mc 1076 - mc 2323*mc 1076 - 2*mc 1891*mc 1076 + 2*mc 1891*mc 2323*mc 1076)) - mc 2499 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2944, KeccakfPermAir.extraction.inter_4824, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4823 c row = (mc 1941 + mc 1062 - mc 2309*mc 1062 - 2*mc 1941*mc 1062 + 2*mc 1941*mc 2309*mc 1062) + 2 * KeccakfPermAir.extraction.inter_4821 c row := by
    simp only [KeccakfPermAir.extraction.inter_4823, KeccakfPermAir.extraction.inter_4822, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4821 c row = (mc 1942 + mc 1063 - mc 2310*mc 1063 - 2*mc 1942*mc 1063 + 2*mc 1942*mc 2310*mc 1063) + 2 * KeccakfPermAir.extraction.inter_4819 c row := by
    simp only [KeccakfPermAir.extraction.inter_4821, KeccakfPermAir.extraction.inter_4820, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4819 c row = (mc 1943 + mc 1064 - mc 2311*mc 1064 - 2*mc 1943*mc 1064 + 2*mc 1943*mc 2311*mc 1064) + 2 * KeccakfPermAir.extraction.inter_4817 c row := by
    simp only [KeccakfPermAir.extraction.inter_4819, KeccakfPermAir.extraction.inter_4818, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4817 c row = (mc 1944 + mc 1065 - mc 2312*mc 1065 - 2*mc 1944*mc 1065 + 2*mc 1944*mc 2312*mc 1065) + 2 * KeccakfPermAir.extraction.inter_4815 c row := by
    simp only [KeccakfPermAir.extraction.inter_4817, KeccakfPermAir.extraction.inter_4816, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4815 c row = (mc 1945 + mc 1066 - mc 2313*mc 1066 - 2*mc 1945*mc 1066 + 2*mc 1945*mc 2313*mc 1066) + 2 * KeccakfPermAir.extraction.inter_4813 c row := by
    simp only [KeccakfPermAir.extraction.inter_4815, KeccakfPermAir.extraction.inter_4814, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4813 c row = (mc 1946 + mc 1067 - mc 2314*mc 1067 - 2*mc 1946*mc 1067 + 2*mc 1946*mc 2314*mc 1067) + 2 * KeccakfPermAir.extraction.inter_4811 c row := by
    simp only [KeccakfPermAir.extraction.inter_4813, KeccakfPermAir.extraction.inter_4812, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4811 c row = (mc 1947 + mc 1068 - mc 2315*mc 1068 - 2*mc 1947*mc 1068 + 2*mc 1947*mc 2315*mc 1068) + 2 * KeccakfPermAir.extraction.inter_4809 c row := by
    simp only [KeccakfPermAir.extraction.inter_4811, KeccakfPermAir.extraction.inter_4810, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4809 c row = (mc 1948 + mc 1069 - mc 2316*mc 1069 - 2*mc 1948*mc 1069 + 2*mc 1948*mc 2316*mc 1069) + 2 * KeccakfPermAir.extraction.inter_4807 c row := by
    simp only [KeccakfPermAir.extraction.inter_4809, KeccakfPermAir.extraction.inter_4808, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4807 c row = (mc 1949 + mc 1070 - mc 2317*mc 1070 - 2*mc 1949*mc 1070 + 2*mc 1949*mc 2317*mc 1070) + 2 * KeccakfPermAir.extraction.inter_4805 c row := by
    simp only [KeccakfPermAir.extraction.inter_4807, KeccakfPermAir.extraction.inter_4806, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4805 c row = (mc 1950 + mc 1071 - mc 2318*mc 1071 - 2*mc 1950*mc 1071 + 2*mc 1950*mc 2318*mc 1071) + 2 * KeccakfPermAir.extraction.inter_4803 c row := by
    simp only [KeccakfPermAir.extraction.inter_4805, KeccakfPermAir.extraction.inter_4804, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4803 c row = (mc 1951 + mc 1072 - mc 2319*mc 1072 - 2*mc 1951*mc 1072 + 2*mc 1951*mc 2319*mc 1072) + 2 * KeccakfPermAir.extraction.inter_4801 c row := by
    simp only [KeccakfPermAir.extraction.inter_4803, KeccakfPermAir.extraction.inter_4802, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4801 c row = (mc 1952 + mc 1073 - mc 2320*mc 1073 - 2*mc 1952*mc 1073 + 2*mc 1952*mc 2320*mc 1073) + 2 * KeccakfPermAir.extraction.inter_4799 c row := by
    simp only [KeccakfPermAir.extraction.inter_4801, KeccakfPermAir.extraction.inter_4800, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4799 c row = (mc 1889 + mc 1074 - mc 2321*mc 1074 - 2*mc 1889*mc 1074 + 2*mc 1889*mc 2321*mc 1074) + 2 * KeccakfPermAir.extraction.inter_4797 c row := by
    simp only [KeccakfPermAir.extraction.inter_4799, KeccakfPermAir.extraction.inter_4798, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4797 c row = (mc 1890 + mc 1075 - mc 2322*mc 1075 - 2*mc 1890*mc 1075 + 2*mc 1890*mc 2322*mc 1075) + 2 * KeccakfPermAir.extraction.inter_4795 c row := by
    simp only [KeccakfPermAir.extraction.inter_4797, KeccakfPermAir.extraction.inter_4796, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4795 c row = (mc 1891 + mc 1076 - mc 2323*mc 1076 - 2*mc 1891*mc 1076 + 2*mc 1891*mc 2323*mc 1076) := by
    simp only [KeccakfPermAir.extraction.inter_4795, KeccakfPermAir.extraction.inter_4794, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2945 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2945 c row) :
    ((mc 1892 + mc 1077 - mc 2324*mc 1077 - 2*mc 1892*mc 1077 + 2*mc 1892*mc 2324*mc 1077) + 2*(mc 1893 + mc 1078 - mc 2325*mc 1078 - 2*mc 1893*mc 1078 + 2*mc 1893*mc 2325*mc 1078) + 4*(mc 1894 + mc 1079 - mc 2326*mc 1079 - 2*mc 1894*mc 1079 + 2*mc 1894*mc 2326*mc 1079) + 8*(mc 1895 + mc 1080 - mc 2327*mc 1080 - 2*mc 1895*mc 1080 + 2*mc 1895*mc 2327*mc 1080) + 16*(mc 1896 + mc 1081 - mc 2328*mc 1081 - 2*mc 1896*mc 1081 + 2*mc 1896*mc 2328*mc 1081) + 32*(mc 1897 + mc 1082 - mc 2329*mc 1082 - 2*mc 1897*mc 1082 + 2*mc 1897*mc 2329*mc 1082) + 64*(mc 1898 + mc 1083 - mc 2330*mc 1083 - 2*mc 1898*mc 1083 + 2*mc 1898*mc 2330*mc 1083) + 128*(mc 1899 + mc 1084 - mc 2331*mc 1084 - 2*mc 1899*mc 1084 + 2*mc 1899*mc 2331*mc 1084) + 256*(mc 1900 + mc 1085 - mc 2332*mc 1085 - 2*mc 1900*mc 1085 + 2*mc 1900*mc 2332*mc 1085) + 512*(mc 1901 + mc 1086 - mc 2333*mc 1086 - 2*mc 1901*mc 1086 + 2*mc 1901*mc 2333*mc 1086) + 1024*(mc 1902 + mc 1087 - mc 2334*mc 1087 - 2*mc 1902*mc 1087 + 2*mc 1902*mc 2334*mc 1087) + 2048*(mc 1903 + mc 1088 - mc 2335*mc 1088 - 2*mc 1903*mc 1088 + 2*mc 1903*mc 2335*mc 1088) + 4096*(mc 1904 + mc 1089 - mc 2336*mc 1089 - 2*mc 1904*mc 1089 + 2*mc 1904*mc 2336*mc 1089) + 8192*(mc 1905 + mc 1090 - mc 2273*mc 1090 - 2*mc 1905*mc 1090 + 2*mc 1905*mc 2273*mc 1090) + 16384*(mc 1906 + mc 1091 - mc 2274*mc 1091 - 2*mc 1906*mc 1091 + 2*mc 1906*mc 2274*mc 1091) + 32768*(mc 1907 + mc 1092 - mc 2275*mc 1092 - 2*mc 1907*mc 1092 + 2*mc 1907*mc 2275*mc 1092)) - mc 2500 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2945, KeccakfPermAir.extraction.inter_4855, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4854 c row = (mc 1893 + mc 1078 - mc 2325*mc 1078 - 2*mc 1893*mc 1078 + 2*mc 1893*mc 2325*mc 1078) + 2 * KeccakfPermAir.extraction.inter_4852 c row := by
    simp only [KeccakfPermAir.extraction.inter_4854, KeccakfPermAir.extraction.inter_4853, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4852 c row = (mc 1894 + mc 1079 - mc 2326*mc 1079 - 2*mc 1894*mc 1079 + 2*mc 1894*mc 2326*mc 1079) + 2 * KeccakfPermAir.extraction.inter_4850 c row := by
    simp only [KeccakfPermAir.extraction.inter_4852, KeccakfPermAir.extraction.inter_4851, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4850 c row = (mc 1895 + mc 1080 - mc 2327*mc 1080 - 2*mc 1895*mc 1080 + 2*mc 1895*mc 2327*mc 1080) + 2 * KeccakfPermAir.extraction.inter_4848 c row := by
    simp only [KeccakfPermAir.extraction.inter_4850, KeccakfPermAir.extraction.inter_4849, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4848 c row = (mc 1896 + mc 1081 - mc 2328*mc 1081 - 2*mc 1896*mc 1081 + 2*mc 1896*mc 2328*mc 1081) + 2 * KeccakfPermAir.extraction.inter_4846 c row := by
    simp only [KeccakfPermAir.extraction.inter_4848, KeccakfPermAir.extraction.inter_4847, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4846 c row = (mc 1897 + mc 1082 - mc 2329*mc 1082 - 2*mc 1897*mc 1082 + 2*mc 1897*mc 2329*mc 1082) + 2 * KeccakfPermAir.extraction.inter_4844 c row := by
    simp only [KeccakfPermAir.extraction.inter_4846, KeccakfPermAir.extraction.inter_4845, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4844 c row = (mc 1898 + mc 1083 - mc 2330*mc 1083 - 2*mc 1898*mc 1083 + 2*mc 1898*mc 2330*mc 1083) + 2 * KeccakfPermAir.extraction.inter_4842 c row := by
    simp only [KeccakfPermAir.extraction.inter_4844, KeccakfPermAir.extraction.inter_4843, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4842 c row = (mc 1899 + mc 1084 - mc 2331*mc 1084 - 2*mc 1899*mc 1084 + 2*mc 1899*mc 2331*mc 1084) + 2 * KeccakfPermAir.extraction.inter_4840 c row := by
    simp only [KeccakfPermAir.extraction.inter_4842, KeccakfPermAir.extraction.inter_4841, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4840 c row = (mc 1900 + mc 1085 - mc 2332*mc 1085 - 2*mc 1900*mc 1085 + 2*mc 1900*mc 2332*mc 1085) + 2 * KeccakfPermAir.extraction.inter_4838 c row := by
    simp only [KeccakfPermAir.extraction.inter_4840, KeccakfPermAir.extraction.inter_4839, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4838 c row = (mc 1901 + mc 1086 - mc 2333*mc 1086 - 2*mc 1901*mc 1086 + 2*mc 1901*mc 2333*mc 1086) + 2 * KeccakfPermAir.extraction.inter_4836 c row := by
    simp only [KeccakfPermAir.extraction.inter_4838, KeccakfPermAir.extraction.inter_4837, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4836 c row = (mc 1902 + mc 1087 - mc 2334*mc 1087 - 2*mc 1902*mc 1087 + 2*mc 1902*mc 2334*mc 1087) + 2 * KeccakfPermAir.extraction.inter_4834 c row := by
    simp only [KeccakfPermAir.extraction.inter_4836, KeccakfPermAir.extraction.inter_4835, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4834 c row = (mc 1903 + mc 1088 - mc 2335*mc 1088 - 2*mc 1903*mc 1088 + 2*mc 1903*mc 2335*mc 1088) + 2 * KeccakfPermAir.extraction.inter_4832 c row := by
    simp only [KeccakfPermAir.extraction.inter_4834, KeccakfPermAir.extraction.inter_4833, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4832 c row = (mc 1904 + mc 1089 - mc 2336*mc 1089 - 2*mc 1904*mc 1089 + 2*mc 1904*mc 2336*mc 1089) + 2 * KeccakfPermAir.extraction.inter_4830 c row := by
    simp only [KeccakfPermAir.extraction.inter_4832, KeccakfPermAir.extraction.inter_4831, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4830 c row = (mc 1905 + mc 1090 - mc 2273*mc 1090 - 2*mc 1905*mc 1090 + 2*mc 1905*mc 2273*mc 1090) + 2 * KeccakfPermAir.extraction.inter_4828 c row := by
    simp only [KeccakfPermAir.extraction.inter_4830, KeccakfPermAir.extraction.inter_4829, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4828 c row = (mc 1906 + mc 1091 - mc 2274*mc 1091 - 2*mc 1906*mc 1091 + 2*mc 1906*mc 2274*mc 1091) + 2 * KeccakfPermAir.extraction.inter_4826 c row := by
    simp only [KeccakfPermAir.extraction.inter_4828, KeccakfPermAir.extraction.inter_4827, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4826 c row = (mc 1907 + mc 1092 - mc 2275*mc 1092 - 2*mc 1907*mc 1092 + 2*mc 1907*mc 2275*mc 1092) := by
    simp only [KeccakfPermAir.extraction.inter_4826, KeccakfPermAir.extraction.inter_4825, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2946 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2946 c row) :
    ((mc 2276 + mc 1485 - mc 1093*mc 1485 - 2*mc 2276*mc 1485 + 2*mc 2276*mc 1093*mc 1485) + 2*(mc 2277 + mc 1486 - mc 1094*mc 1486 - 2*mc 2277*mc 1486 + 2*mc 2277*mc 1094*mc 1486) + 4*(mc 2278 + mc 1487 - mc 1095*mc 1487 - 2*mc 2278*mc 1487 + 2*mc 2278*mc 1095*mc 1487) + 8*(mc 2279 + mc 1488 - mc 1096*mc 1488 - 2*mc 2279*mc 1488 + 2*mc 2279*mc 1096*mc 1488) + 16*(mc 2280 + mc 1489 - mc 1097*mc 1489 - 2*mc 2280*mc 1489 + 2*mc 2280*mc 1097*mc 1489) + 32*(mc 2281 + mc 1490 - mc 1098*mc 1490 - 2*mc 2281*mc 1490 + 2*mc 2281*mc 1098*mc 1490) + 64*(mc 2282 + mc 1491 - mc 1099*mc 1491 - 2*mc 2282*mc 1491 + 2*mc 2282*mc 1099*mc 1491) + 128*(mc 2283 + mc 1492 - mc 1100*mc 1492 - 2*mc 2283*mc 1492 + 2*mc 2283*mc 1100*mc 1492) + 256*(mc 2284 + mc 1493 - mc 1101*mc 1493 - 2*mc 2284*mc 1493 + 2*mc 2284*mc 1101*mc 1493) + 512*(mc 2285 + mc 1494 - mc 1102*mc 1494 - 2*mc 2285*mc 1494 + 2*mc 2285*mc 1102*mc 1494) + 1024*(mc 2286 + mc 1495 - mc 1103*mc 1495 - 2*mc 2286*mc 1495 + 2*mc 2286*mc 1103*mc 1495) + 2048*(mc 2287 + mc 1496 - mc 1104*mc 1496 - 2*mc 2287*mc 1496 + 2*mc 2287*mc 1104*mc 1496) + 4096*(mc 2288 + mc 1497 - mc 1105*mc 1497 - 2*mc 2288*mc 1497 + 2*mc 2288*mc 1105*mc 1497) + 8192*(mc 2289 + mc 1498 - mc 1106*mc 1498 - 2*mc 2289*mc 1498 + 2*mc 2289*mc 1106*mc 1498) + 16384*(mc 2290 + mc 1499 - mc 1107*mc 1499 - 2*mc 2290*mc 1499 + 2*mc 2290*mc 1107*mc 1499) + 32768*(mc 2291 + mc 1500 - mc 1108*mc 1500 - 2*mc 2291*mc 1500 + 2*mc 2291*mc 1108*mc 1500)) - mc 2501 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2946, KeccakfPermAir.extraction.inter_4886, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4885 c row = (mc 2277 + mc 1486 - mc 1094*mc 1486 - 2*mc 2277*mc 1486 + 2*mc 2277*mc 1094*mc 1486) + 2 * KeccakfPermAir.extraction.inter_4883 c row := by
    simp only [KeccakfPermAir.extraction.inter_4885, KeccakfPermAir.extraction.inter_4884, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4883 c row = (mc 2278 + mc 1487 - mc 1095*mc 1487 - 2*mc 2278*mc 1487 + 2*mc 2278*mc 1095*mc 1487) + 2 * KeccakfPermAir.extraction.inter_4881 c row := by
    simp only [KeccakfPermAir.extraction.inter_4883, KeccakfPermAir.extraction.inter_4882, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4881 c row = (mc 2279 + mc 1488 - mc 1096*mc 1488 - 2*mc 2279*mc 1488 + 2*mc 2279*mc 1096*mc 1488) + 2 * KeccakfPermAir.extraction.inter_4879 c row := by
    simp only [KeccakfPermAir.extraction.inter_4881, KeccakfPermAir.extraction.inter_4880, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4879 c row = (mc 2280 + mc 1489 - mc 1097*mc 1489 - 2*mc 2280*mc 1489 + 2*mc 2280*mc 1097*mc 1489) + 2 * KeccakfPermAir.extraction.inter_4877 c row := by
    simp only [KeccakfPermAir.extraction.inter_4879, KeccakfPermAir.extraction.inter_4878, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4877 c row = (mc 2281 + mc 1490 - mc 1098*mc 1490 - 2*mc 2281*mc 1490 + 2*mc 2281*mc 1098*mc 1490) + 2 * KeccakfPermAir.extraction.inter_4875 c row := by
    simp only [KeccakfPermAir.extraction.inter_4877, KeccakfPermAir.extraction.inter_4876, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4875 c row = (mc 2282 + mc 1491 - mc 1099*mc 1491 - 2*mc 2282*mc 1491 + 2*mc 2282*mc 1099*mc 1491) + 2 * KeccakfPermAir.extraction.inter_4873 c row := by
    simp only [KeccakfPermAir.extraction.inter_4875, KeccakfPermAir.extraction.inter_4874, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4873 c row = (mc 2283 + mc 1492 - mc 1100*mc 1492 - 2*mc 2283*mc 1492 + 2*mc 2283*mc 1100*mc 1492) + 2 * KeccakfPermAir.extraction.inter_4871 c row := by
    simp only [KeccakfPermAir.extraction.inter_4873, KeccakfPermAir.extraction.inter_4872, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4871 c row = (mc 2284 + mc 1493 - mc 1101*mc 1493 - 2*mc 2284*mc 1493 + 2*mc 2284*mc 1101*mc 1493) + 2 * KeccakfPermAir.extraction.inter_4869 c row := by
    simp only [KeccakfPermAir.extraction.inter_4871, KeccakfPermAir.extraction.inter_4870, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4869 c row = (mc 2285 + mc 1494 - mc 1102*mc 1494 - 2*mc 2285*mc 1494 + 2*mc 2285*mc 1102*mc 1494) + 2 * KeccakfPermAir.extraction.inter_4867 c row := by
    simp only [KeccakfPermAir.extraction.inter_4869, KeccakfPermAir.extraction.inter_4868, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4867 c row = (mc 2286 + mc 1495 - mc 1103*mc 1495 - 2*mc 2286*mc 1495 + 2*mc 2286*mc 1103*mc 1495) + 2 * KeccakfPermAir.extraction.inter_4865 c row := by
    simp only [KeccakfPermAir.extraction.inter_4867, KeccakfPermAir.extraction.inter_4866, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4865 c row = (mc 2287 + mc 1496 - mc 1104*mc 1496 - 2*mc 2287*mc 1496 + 2*mc 2287*mc 1104*mc 1496) + 2 * KeccakfPermAir.extraction.inter_4863 c row := by
    simp only [KeccakfPermAir.extraction.inter_4865, KeccakfPermAir.extraction.inter_4864, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4863 c row = (mc 2288 + mc 1497 - mc 1105*mc 1497 - 2*mc 2288*mc 1497 + 2*mc 2288*mc 1105*mc 1497) + 2 * KeccakfPermAir.extraction.inter_4861 c row := by
    simp only [KeccakfPermAir.extraction.inter_4863, KeccakfPermAir.extraction.inter_4862, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4861 c row = (mc 2289 + mc 1498 - mc 1106*mc 1498 - 2*mc 2289*mc 1498 + 2*mc 2289*mc 1106*mc 1498) + 2 * KeccakfPermAir.extraction.inter_4859 c row := by
    simp only [KeccakfPermAir.extraction.inter_4861, KeccakfPermAir.extraction.inter_4860, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4859 c row = (mc 2290 + mc 1499 - mc 1107*mc 1499 - 2*mc 2290*mc 1499 + 2*mc 2290*mc 1107*mc 1499) + 2 * KeccakfPermAir.extraction.inter_4857 c row := by
    simp only [KeccakfPermAir.extraction.inter_4859, KeccakfPermAir.extraction.inter_4858, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4857 c row = (mc 2291 + mc 1500 - mc 1108*mc 1500 - 2*mc 2291*mc 1500 + 2*mc 2291*mc 1108*mc 1500) := by
    simp only [KeccakfPermAir.extraction.inter_4857, KeccakfPermAir.extraction.inter_4856, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2947 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2947 c row) :
    ((mc 2292 + mc 1501 - mc 1109*mc 1501 - 2*mc 2292*mc 1501 + 2*mc 2292*mc 1109*mc 1501) + 2*(mc 2293 + mc 1502 - mc 1110*mc 1502 - 2*mc 2293*mc 1502 + 2*mc 2293*mc 1110*mc 1502) + 4*(mc 2294 + mc 1503 - mc 1111*mc 1503 - 2*mc 2294*mc 1503 + 2*mc 2294*mc 1111*mc 1503) + 8*(mc 2295 + mc 1504 - mc 1112*mc 1504 - 2*mc 2295*mc 1504 + 2*mc 2295*mc 1112*mc 1504) + 16*(mc 2296 + mc 1441 - mc 1113*mc 1441 - 2*mc 2296*mc 1441 + 2*mc 2296*mc 1113*mc 1441) + 32*(mc 2297 + mc 1442 - mc 1114*mc 1442 - 2*mc 2297*mc 1442 + 2*mc 2297*mc 1114*mc 1442) + 64*(mc 2298 + mc 1443 - mc 1115*mc 1443 - 2*mc 2298*mc 1443 + 2*mc 2298*mc 1115*mc 1443) + 128*(mc 2299 + mc 1444 - mc 1116*mc 1444 - 2*mc 2299*mc 1444 + 2*mc 2299*mc 1116*mc 1444) + 256*(mc 2300 + mc 1445 - mc 1117*mc 1445 - 2*mc 2300*mc 1445 + 2*mc 2300*mc 1117*mc 1445) + 512*(mc 2301 + mc 1446 - mc 1118*mc 1446 - 2*mc 2301*mc 1446 + 2*mc 2301*mc 1118*mc 1446) + 1024*(mc 2302 + mc 1447 - mc 1119*mc 1447 - 2*mc 2302*mc 1447 + 2*mc 2302*mc 1119*mc 1447) + 2048*(mc 2303 + mc 1448 - mc 1120*mc 1448 - 2*mc 2303*mc 1448 + 2*mc 2303*mc 1120*mc 1448) + 4096*(mc 2304 + mc 1449 - mc 1057*mc 1449 - 2*mc 2304*mc 1449 + 2*mc 2304*mc 1057*mc 1449) + 8192*(mc 2305 + mc 1450 - mc 1058*mc 1450 - 2*mc 2305*mc 1450 + 2*mc 2305*mc 1058*mc 1450) + 16384*(mc 2306 + mc 1451 - mc 1059*mc 1451 - 2*mc 2306*mc 1451 + 2*mc 2306*mc 1059*mc 1451) + 32768*(mc 2307 + mc 1452 - mc 1060*mc 1452 - 2*mc 2307*mc 1452 + 2*mc 2307*mc 1060*mc 1452)) - mc 2502 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2947, KeccakfPermAir.extraction.inter_4917, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4916 c row = (mc 2293 + mc 1502 - mc 1110*mc 1502 - 2*mc 2293*mc 1502 + 2*mc 2293*mc 1110*mc 1502) + 2 * KeccakfPermAir.extraction.inter_4914 c row := by
    simp only [KeccakfPermAir.extraction.inter_4916, KeccakfPermAir.extraction.inter_4915, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4914 c row = (mc 2294 + mc 1503 - mc 1111*mc 1503 - 2*mc 2294*mc 1503 + 2*mc 2294*mc 1111*mc 1503) + 2 * KeccakfPermAir.extraction.inter_4912 c row := by
    simp only [KeccakfPermAir.extraction.inter_4914, KeccakfPermAir.extraction.inter_4913, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4912 c row = (mc 2295 + mc 1504 - mc 1112*mc 1504 - 2*mc 2295*mc 1504 + 2*mc 2295*mc 1112*mc 1504) + 2 * KeccakfPermAir.extraction.inter_4910 c row := by
    simp only [KeccakfPermAir.extraction.inter_4912, KeccakfPermAir.extraction.inter_4911, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4910 c row = (mc 2296 + mc 1441 - mc 1113*mc 1441 - 2*mc 2296*mc 1441 + 2*mc 2296*mc 1113*mc 1441) + 2 * KeccakfPermAir.extraction.inter_4908 c row := by
    simp only [KeccakfPermAir.extraction.inter_4910, KeccakfPermAir.extraction.inter_4909, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4908 c row = (mc 2297 + mc 1442 - mc 1114*mc 1442 - 2*mc 2297*mc 1442 + 2*mc 2297*mc 1114*mc 1442) + 2 * KeccakfPermAir.extraction.inter_4906 c row := by
    simp only [KeccakfPermAir.extraction.inter_4908, KeccakfPermAir.extraction.inter_4907, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4906 c row = (mc 2298 + mc 1443 - mc 1115*mc 1443 - 2*mc 2298*mc 1443 + 2*mc 2298*mc 1115*mc 1443) + 2 * KeccakfPermAir.extraction.inter_4904 c row := by
    simp only [KeccakfPermAir.extraction.inter_4906, KeccakfPermAir.extraction.inter_4905, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4904 c row = (mc 2299 + mc 1444 - mc 1116*mc 1444 - 2*mc 2299*mc 1444 + 2*mc 2299*mc 1116*mc 1444) + 2 * KeccakfPermAir.extraction.inter_4902 c row := by
    simp only [KeccakfPermAir.extraction.inter_4904, KeccakfPermAir.extraction.inter_4903, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4902 c row = (mc 2300 + mc 1445 - mc 1117*mc 1445 - 2*mc 2300*mc 1445 + 2*mc 2300*mc 1117*mc 1445) + 2 * KeccakfPermAir.extraction.inter_4900 c row := by
    simp only [KeccakfPermAir.extraction.inter_4902, KeccakfPermAir.extraction.inter_4901, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4900 c row = (mc 2301 + mc 1446 - mc 1118*mc 1446 - 2*mc 2301*mc 1446 + 2*mc 2301*mc 1118*mc 1446) + 2 * KeccakfPermAir.extraction.inter_4898 c row := by
    simp only [KeccakfPermAir.extraction.inter_4900, KeccakfPermAir.extraction.inter_4899, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4898 c row = (mc 2302 + mc 1447 - mc 1119*mc 1447 - 2*mc 2302*mc 1447 + 2*mc 2302*mc 1119*mc 1447) + 2 * KeccakfPermAir.extraction.inter_4896 c row := by
    simp only [KeccakfPermAir.extraction.inter_4898, KeccakfPermAir.extraction.inter_4897, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4896 c row = (mc 2303 + mc 1448 - mc 1120*mc 1448 - 2*mc 2303*mc 1448 + 2*mc 2303*mc 1120*mc 1448) + 2 * KeccakfPermAir.extraction.inter_4894 c row := by
    simp only [KeccakfPermAir.extraction.inter_4896, KeccakfPermAir.extraction.inter_4895, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4894 c row = (mc 2304 + mc 1449 - mc 1057*mc 1449 - 2*mc 2304*mc 1449 + 2*mc 2304*mc 1057*mc 1449) + 2 * KeccakfPermAir.extraction.inter_4892 c row := by
    simp only [KeccakfPermAir.extraction.inter_4894, KeccakfPermAir.extraction.inter_4893, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4892 c row = (mc 2305 + mc 1450 - mc 1058*mc 1450 - 2*mc 2305*mc 1450 + 2*mc 2305*mc 1058*mc 1450) + 2 * KeccakfPermAir.extraction.inter_4890 c row := by
    simp only [KeccakfPermAir.extraction.inter_4892, KeccakfPermAir.extraction.inter_4891, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4890 c row = (mc 2306 + mc 1451 - mc 1059*mc 1451 - 2*mc 2306*mc 1451 + 2*mc 2306*mc 1059*mc 1451) + 2 * KeccakfPermAir.extraction.inter_4888 c row := by
    simp only [KeccakfPermAir.extraction.inter_4890, KeccakfPermAir.extraction.inter_4889, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4888 c row = (mc 2307 + mc 1452 - mc 1060*mc 1452 - 2*mc 2307*mc 1452 + 2*mc 2307*mc 1060*mc 1452) := by
    simp only [KeccakfPermAir.extraction.inter_4888, KeccakfPermAir.extraction.inter_4887, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2948 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2948 c row) :
    ((mc 2308 + mc 1453 - mc 1061*mc 1453 - 2*mc 2308*mc 1453 + 2*mc 2308*mc 1061*mc 1453) + 2*(mc 2309 + mc 1454 - mc 1062*mc 1454 - 2*mc 2309*mc 1454 + 2*mc 2309*mc 1062*mc 1454) + 4*(mc 2310 + mc 1455 - mc 1063*mc 1455 - 2*mc 2310*mc 1455 + 2*mc 2310*mc 1063*mc 1455) + 8*(mc 2311 + mc 1456 - mc 1064*mc 1456 - 2*mc 2311*mc 1456 + 2*mc 2311*mc 1064*mc 1456) + 16*(mc 2312 + mc 1457 - mc 1065*mc 1457 - 2*mc 2312*mc 1457 + 2*mc 2312*mc 1065*mc 1457) + 32*(mc 2313 + mc 1458 - mc 1066*mc 1458 - 2*mc 2313*mc 1458 + 2*mc 2313*mc 1066*mc 1458) + 64*(mc 2314 + mc 1459 - mc 1067*mc 1459 - 2*mc 2314*mc 1459 + 2*mc 2314*mc 1067*mc 1459) + 128*(mc 2315 + mc 1460 - mc 1068*mc 1460 - 2*mc 2315*mc 1460 + 2*mc 2315*mc 1068*mc 1460) + 256*(mc 2316 + mc 1461 - mc 1069*mc 1461 - 2*mc 2316*mc 1461 + 2*mc 2316*mc 1069*mc 1461) + 512*(mc 2317 + mc 1462 - mc 1070*mc 1462 - 2*mc 2317*mc 1462 + 2*mc 2317*mc 1070*mc 1462) + 1024*(mc 2318 + mc 1463 - mc 1071*mc 1463 - 2*mc 2318*mc 1463 + 2*mc 2318*mc 1071*mc 1463) + 2048*(mc 2319 + mc 1464 - mc 1072*mc 1464 - 2*mc 2319*mc 1464 + 2*mc 2319*mc 1072*mc 1464) + 4096*(mc 2320 + mc 1465 - mc 1073*mc 1465 - 2*mc 2320*mc 1465 + 2*mc 2320*mc 1073*mc 1465) + 8192*(mc 2321 + mc 1466 - mc 1074*mc 1466 - 2*mc 2321*mc 1466 + 2*mc 2321*mc 1074*mc 1466) + 16384*(mc 2322 + mc 1467 - mc 1075*mc 1467 - 2*mc 2322*mc 1467 + 2*mc 2322*mc 1075*mc 1467) + 32768*(mc 2323 + mc 1468 - mc 1076*mc 1468 - 2*mc 2323*mc 1468 + 2*mc 2323*mc 1076*mc 1468)) - mc 2503 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2948, KeccakfPermAir.extraction.inter_4948, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4947 c row = (mc 2309 + mc 1454 - mc 1062*mc 1454 - 2*mc 2309*mc 1454 + 2*mc 2309*mc 1062*mc 1454) + 2 * KeccakfPermAir.extraction.inter_4945 c row := by
    simp only [KeccakfPermAir.extraction.inter_4947, KeccakfPermAir.extraction.inter_4946, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4945 c row = (mc 2310 + mc 1455 - mc 1063*mc 1455 - 2*mc 2310*mc 1455 + 2*mc 2310*mc 1063*mc 1455) + 2 * KeccakfPermAir.extraction.inter_4943 c row := by
    simp only [KeccakfPermAir.extraction.inter_4945, KeccakfPermAir.extraction.inter_4944, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4943 c row = (mc 2311 + mc 1456 - mc 1064*mc 1456 - 2*mc 2311*mc 1456 + 2*mc 2311*mc 1064*mc 1456) + 2 * KeccakfPermAir.extraction.inter_4941 c row := by
    simp only [KeccakfPermAir.extraction.inter_4943, KeccakfPermAir.extraction.inter_4942, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4941 c row = (mc 2312 + mc 1457 - mc 1065*mc 1457 - 2*mc 2312*mc 1457 + 2*mc 2312*mc 1065*mc 1457) + 2 * KeccakfPermAir.extraction.inter_4939 c row := by
    simp only [KeccakfPermAir.extraction.inter_4941, KeccakfPermAir.extraction.inter_4940, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4939 c row = (mc 2313 + mc 1458 - mc 1066*mc 1458 - 2*mc 2313*mc 1458 + 2*mc 2313*mc 1066*mc 1458) + 2 * KeccakfPermAir.extraction.inter_4937 c row := by
    simp only [KeccakfPermAir.extraction.inter_4939, KeccakfPermAir.extraction.inter_4938, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4937 c row = (mc 2314 + mc 1459 - mc 1067*mc 1459 - 2*mc 2314*mc 1459 + 2*mc 2314*mc 1067*mc 1459) + 2 * KeccakfPermAir.extraction.inter_4935 c row := by
    simp only [KeccakfPermAir.extraction.inter_4937, KeccakfPermAir.extraction.inter_4936, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4935 c row = (mc 2315 + mc 1460 - mc 1068*mc 1460 - 2*mc 2315*mc 1460 + 2*mc 2315*mc 1068*mc 1460) + 2 * KeccakfPermAir.extraction.inter_4933 c row := by
    simp only [KeccakfPermAir.extraction.inter_4935, KeccakfPermAir.extraction.inter_4934, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4933 c row = (mc 2316 + mc 1461 - mc 1069*mc 1461 - 2*mc 2316*mc 1461 + 2*mc 2316*mc 1069*mc 1461) + 2 * KeccakfPermAir.extraction.inter_4931 c row := by
    simp only [KeccakfPermAir.extraction.inter_4933, KeccakfPermAir.extraction.inter_4932, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4931 c row = (mc 2317 + mc 1462 - mc 1070*mc 1462 - 2*mc 2317*mc 1462 + 2*mc 2317*mc 1070*mc 1462) + 2 * KeccakfPermAir.extraction.inter_4929 c row := by
    simp only [KeccakfPermAir.extraction.inter_4931, KeccakfPermAir.extraction.inter_4930, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4929 c row = (mc 2318 + mc 1463 - mc 1071*mc 1463 - 2*mc 2318*mc 1463 + 2*mc 2318*mc 1071*mc 1463) + 2 * KeccakfPermAir.extraction.inter_4927 c row := by
    simp only [KeccakfPermAir.extraction.inter_4929, KeccakfPermAir.extraction.inter_4928, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4927 c row = (mc 2319 + mc 1464 - mc 1072*mc 1464 - 2*mc 2319*mc 1464 + 2*mc 2319*mc 1072*mc 1464) + 2 * KeccakfPermAir.extraction.inter_4925 c row := by
    simp only [KeccakfPermAir.extraction.inter_4927, KeccakfPermAir.extraction.inter_4926, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4925 c row = (mc 2320 + mc 1465 - mc 1073*mc 1465 - 2*mc 2320*mc 1465 + 2*mc 2320*mc 1073*mc 1465) + 2 * KeccakfPermAir.extraction.inter_4923 c row := by
    simp only [KeccakfPermAir.extraction.inter_4925, KeccakfPermAir.extraction.inter_4924, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4923 c row = (mc 2321 + mc 1466 - mc 1074*mc 1466 - 2*mc 2321*mc 1466 + 2*mc 2321*mc 1074*mc 1466) + 2 * KeccakfPermAir.extraction.inter_4921 c row := by
    simp only [KeccakfPermAir.extraction.inter_4923, KeccakfPermAir.extraction.inter_4922, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4921 c row = (mc 2322 + mc 1467 - mc 1075*mc 1467 - 2*mc 2322*mc 1467 + 2*mc 2322*mc 1075*mc 1467) + 2 * KeccakfPermAir.extraction.inter_4919 c row := by
    simp only [KeccakfPermAir.extraction.inter_4921, KeccakfPermAir.extraction.inter_4920, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4919 c row = (mc 2323 + mc 1468 - mc 1076*mc 1468 - 2*mc 2323*mc 1468 + 2*mc 2323*mc 1076*mc 1468) := by
    simp only [KeccakfPermAir.extraction.inter_4919, KeccakfPermAir.extraction.inter_4918, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2949 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2949 c row) :
    ((mc 2324 + mc 1469 - mc 1077*mc 1469 - 2*mc 2324*mc 1469 + 2*mc 2324*mc 1077*mc 1469) + 2*(mc 2325 + mc 1470 - mc 1078*mc 1470 - 2*mc 2325*mc 1470 + 2*mc 2325*mc 1078*mc 1470) + 4*(mc 2326 + mc 1471 - mc 1079*mc 1471 - 2*mc 2326*mc 1471 + 2*mc 2326*mc 1079*mc 1471) + 8*(mc 2327 + mc 1472 - mc 1080*mc 1472 - 2*mc 2327*mc 1472 + 2*mc 2327*mc 1080*mc 1472) + 16*(mc 2328 + mc 1473 - mc 1081*mc 1473 - 2*mc 2328*mc 1473 + 2*mc 2328*mc 1081*mc 1473) + 32*(mc 2329 + mc 1474 - mc 1082*mc 1474 - 2*mc 2329*mc 1474 + 2*mc 2329*mc 1082*mc 1474) + 64*(mc 2330 + mc 1475 - mc 1083*mc 1475 - 2*mc 2330*mc 1475 + 2*mc 2330*mc 1083*mc 1475) + 128*(mc 2331 + mc 1476 - mc 1084*mc 1476 - 2*mc 2331*mc 1476 + 2*mc 2331*mc 1084*mc 1476) + 256*(mc 2332 + mc 1477 - mc 1085*mc 1477 - 2*mc 2332*mc 1477 + 2*mc 2332*mc 1085*mc 1477) + 512*(mc 2333 + mc 1478 - mc 1086*mc 1478 - 2*mc 2333*mc 1478 + 2*mc 2333*mc 1086*mc 1478) + 1024*(mc 2334 + mc 1479 - mc 1087*mc 1479 - 2*mc 2334*mc 1479 + 2*mc 2334*mc 1087*mc 1479) + 2048*(mc 2335 + mc 1480 - mc 1088*mc 1480 - 2*mc 2335*mc 1480 + 2*mc 2335*mc 1088*mc 1480) + 4096*(mc 2336 + mc 1481 - mc 1089*mc 1481 - 2*mc 2336*mc 1481 + 2*mc 2336*mc 1089*mc 1481) + 8192*(mc 2273 + mc 1482 - mc 1090*mc 1482 - 2*mc 2273*mc 1482 + 2*mc 2273*mc 1090*mc 1482) + 16384*(mc 2274 + mc 1483 - mc 1091*mc 1483 - 2*mc 2274*mc 1483 + 2*mc 2274*mc 1091*mc 1483) + 32768*(mc 2275 + mc 1484 - mc 1092*mc 1484 - 2*mc 2275*mc 1484 + 2*mc 2275*mc 1092*mc 1484)) - mc 2504 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2949, KeccakfPermAir.extraction.inter_4979, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_4978 c row = (mc 2325 + mc 1470 - mc 1078*mc 1470 - 2*mc 2325*mc 1470 + 2*mc 2325*mc 1078*mc 1470) + 2 * KeccakfPermAir.extraction.inter_4976 c row := by
    simp only [KeccakfPermAir.extraction.inter_4978, KeccakfPermAir.extraction.inter_4977, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_4976 c row = (mc 2326 + mc 1471 - mc 1079*mc 1471 - 2*mc 2326*mc 1471 + 2*mc 2326*mc 1079*mc 1471) + 2 * KeccakfPermAir.extraction.inter_4974 c row := by
    simp only [KeccakfPermAir.extraction.inter_4976, KeccakfPermAir.extraction.inter_4975, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_4974 c row = (mc 2327 + mc 1472 - mc 1080*mc 1472 - 2*mc 2327*mc 1472 + 2*mc 2327*mc 1080*mc 1472) + 2 * KeccakfPermAir.extraction.inter_4972 c row := by
    simp only [KeccakfPermAir.extraction.inter_4974, KeccakfPermAir.extraction.inter_4973, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_4972 c row = (mc 2328 + mc 1473 - mc 1081*mc 1473 - 2*mc 2328*mc 1473 + 2*mc 2328*mc 1081*mc 1473) + 2 * KeccakfPermAir.extraction.inter_4970 c row := by
    simp only [KeccakfPermAir.extraction.inter_4972, KeccakfPermAir.extraction.inter_4971, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_4970 c row = (mc 2329 + mc 1474 - mc 1082*mc 1474 - 2*mc 2329*mc 1474 + 2*mc 2329*mc 1082*mc 1474) + 2 * KeccakfPermAir.extraction.inter_4968 c row := by
    simp only [KeccakfPermAir.extraction.inter_4970, KeccakfPermAir.extraction.inter_4969, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4968 c row = (mc 2330 + mc 1475 - mc 1083*mc 1475 - 2*mc 2330*mc 1475 + 2*mc 2330*mc 1083*mc 1475) + 2 * KeccakfPermAir.extraction.inter_4966 c row := by
    simp only [KeccakfPermAir.extraction.inter_4968, KeccakfPermAir.extraction.inter_4967, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4966 c row = (mc 2331 + mc 1476 - mc 1084*mc 1476 - 2*mc 2331*mc 1476 + 2*mc 2331*mc 1084*mc 1476) + 2 * KeccakfPermAir.extraction.inter_4964 c row := by
    simp only [KeccakfPermAir.extraction.inter_4966, KeccakfPermAir.extraction.inter_4965, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4964 c row = (mc 2332 + mc 1477 - mc 1085*mc 1477 - 2*mc 2332*mc 1477 + 2*mc 2332*mc 1085*mc 1477) + 2 * KeccakfPermAir.extraction.inter_4962 c row := by
    simp only [KeccakfPermAir.extraction.inter_4964, KeccakfPermAir.extraction.inter_4963, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4962 c row = (mc 2333 + mc 1478 - mc 1086*mc 1478 - 2*mc 2333*mc 1478 + 2*mc 2333*mc 1086*mc 1478) + 2 * KeccakfPermAir.extraction.inter_4960 c row := by
    simp only [KeccakfPermAir.extraction.inter_4962, KeccakfPermAir.extraction.inter_4961, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4960 c row = (mc 2334 + mc 1479 - mc 1087*mc 1479 - 2*mc 2334*mc 1479 + 2*mc 2334*mc 1087*mc 1479) + 2 * KeccakfPermAir.extraction.inter_4958 c row := by
    simp only [KeccakfPermAir.extraction.inter_4960, KeccakfPermAir.extraction.inter_4959, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4958 c row = (mc 2335 + mc 1480 - mc 1088*mc 1480 - 2*mc 2335*mc 1480 + 2*mc 2335*mc 1088*mc 1480) + 2 * KeccakfPermAir.extraction.inter_4956 c row := by
    simp only [KeccakfPermAir.extraction.inter_4958, KeccakfPermAir.extraction.inter_4957, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4956 c row = (mc 2336 + mc 1481 - mc 1089*mc 1481 - 2*mc 2336*mc 1481 + 2*mc 2336*mc 1089*mc 1481) + 2 * KeccakfPermAir.extraction.inter_4954 c row := by
    simp only [KeccakfPermAir.extraction.inter_4956, KeccakfPermAir.extraction.inter_4955, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4954 c row = (mc 2273 + mc 1482 - mc 1090*mc 1482 - 2*mc 2273*mc 1482 + 2*mc 2273*mc 1090*mc 1482) + 2 * KeccakfPermAir.extraction.inter_4952 c row := by
    simp only [KeccakfPermAir.extraction.inter_4954, KeccakfPermAir.extraction.inter_4953, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4952 c row = (mc 2274 + mc 1483 - mc 1091*mc 1483 - 2*mc 2274*mc 1483 + 2*mc 2274*mc 1091*mc 1483) + 2 * KeccakfPermAir.extraction.inter_4950 c row := by
    simp only [KeccakfPermAir.extraction.inter_4952, KeccakfPermAir.extraction.inter_4951, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4950 c row = (mc 2275 + mc 1484 - mc 1092*mc 1484 - 2*mc 2275*mc 1484 + 2*mc 2275*mc 1092*mc 1484) := by
    simp only [KeccakfPermAir.extraction.inter_4950, KeccakfPermAir.extraction.inter_4949, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2950 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2950 c row) :
    ((mc 992 + mc 1736 - mc 1371*mc 1736 - 2*mc 992*mc 1736 + 2*mc 992*mc 1371*mc 1736) + 2*(mc 929 + mc 1737 - mc 1372*mc 1737 - 2*mc 929*mc 1737 + 2*mc 929*mc 1372*mc 1737) + 4*(mc 930 + mc 1738 - mc 1373*mc 1738 - 2*mc 930*mc 1738 + 2*mc 930*mc 1373*mc 1738) + 8*(mc 931 + mc 1739 - mc 1374*mc 1739 - 2*mc 931*mc 1739 + 2*mc 931*mc 1374*mc 1739) + 16*(mc 932 + mc 1740 - mc 1375*mc 1740 - 2*mc 932*mc 1740 + 2*mc 932*mc 1375*mc 1740) + 32*(mc 933 + mc 1741 - mc 1376*mc 1741 - 2*mc 933*mc 1741 + 2*mc 933*mc 1376*mc 1741) + 64*(mc 934 + mc 1742 - mc 1313*mc 1742 - 2*mc 934*mc 1742 + 2*mc 934*mc 1313*mc 1742) + 128*(mc 935 + mc 1743 - mc 1314*mc 1743 - 2*mc 935*mc 1743 + 2*mc 935*mc 1314*mc 1743) + 256*(mc 936 + mc 1744 - mc 1315*mc 1744 - 2*mc 936*mc 1744 + 2*mc 936*mc 1315*mc 1744) + 512*(mc 937 + mc 1745 - mc 1316*mc 1745 - 2*mc 937*mc 1745 + 2*mc 937*mc 1316*mc 1745) + 1024*(mc 938 + mc 1746 - mc 1317*mc 1746 - 2*mc 938*mc 1746 + 2*mc 938*mc 1317*mc 1746) + 2048*(mc 939 + mc 1747 - mc 1318*mc 1747 - 2*mc 939*mc 1747 + 2*mc 939*mc 1318*mc 1747) + 4096*(mc 940 + mc 1748 - mc 1319*mc 1748 - 2*mc 940*mc 1748 + 2*mc 940*mc 1319*mc 1748) + 8192*(mc 941 + mc 1749 - mc 1320*mc 1749 - 2*mc 941*mc 1749 + 2*mc 941*mc 1320*mc 1749) + 16384*(mc 942 + mc 1750 - mc 1321*mc 1750 - 2*mc 942*mc 1750 + 2*mc 942*mc 1321*mc 1750) + 32768*(mc 943 + mc 1751 - mc 1322*mc 1751 - 2*mc 943*mc 1751 + 2*mc 943*mc 1322*mc 1751)) - mc 2505 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2950, KeccakfPermAir.extraction.inter_5010, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5009 c row = (mc 929 + mc 1737 - mc 1372*mc 1737 - 2*mc 929*mc 1737 + 2*mc 929*mc 1372*mc 1737) + 2 * KeccakfPermAir.extraction.inter_5007 c row := by
    simp only [KeccakfPermAir.extraction.inter_5009, KeccakfPermAir.extraction.inter_5008, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5007 c row = (mc 930 + mc 1738 - mc 1373*mc 1738 - 2*mc 930*mc 1738 + 2*mc 930*mc 1373*mc 1738) + 2 * KeccakfPermAir.extraction.inter_5005 c row := by
    simp only [KeccakfPermAir.extraction.inter_5007, KeccakfPermAir.extraction.inter_5006, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5005 c row = (mc 931 + mc 1739 - mc 1374*mc 1739 - 2*mc 931*mc 1739 + 2*mc 931*mc 1374*mc 1739) + 2 * KeccakfPermAir.extraction.inter_5003 c row := by
    simp only [KeccakfPermAir.extraction.inter_5005, KeccakfPermAir.extraction.inter_5004, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5003 c row = (mc 932 + mc 1740 - mc 1375*mc 1740 - 2*mc 932*mc 1740 + 2*mc 932*mc 1375*mc 1740) + 2 * KeccakfPermAir.extraction.inter_5001 c row := by
    simp only [KeccakfPermAir.extraction.inter_5003, KeccakfPermAir.extraction.inter_5002, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5001 c row = (mc 933 + mc 1741 - mc 1376*mc 1741 - 2*mc 933*mc 1741 + 2*mc 933*mc 1376*mc 1741) + 2 * KeccakfPermAir.extraction.inter_4999 c row := by
    simp only [KeccakfPermAir.extraction.inter_5001, KeccakfPermAir.extraction.inter_5000, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_4999 c row = (mc 934 + mc 1742 - mc 1313*mc 1742 - 2*mc 934*mc 1742 + 2*mc 934*mc 1313*mc 1742) + 2 * KeccakfPermAir.extraction.inter_4997 c row := by
    simp only [KeccakfPermAir.extraction.inter_4999, KeccakfPermAir.extraction.inter_4998, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_4997 c row = (mc 935 + mc 1743 - mc 1314*mc 1743 - 2*mc 935*mc 1743 + 2*mc 935*mc 1314*mc 1743) + 2 * KeccakfPermAir.extraction.inter_4995 c row := by
    simp only [KeccakfPermAir.extraction.inter_4997, KeccakfPermAir.extraction.inter_4996, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_4995 c row = (mc 936 + mc 1744 - mc 1315*mc 1744 - 2*mc 936*mc 1744 + 2*mc 936*mc 1315*mc 1744) + 2 * KeccakfPermAir.extraction.inter_4993 c row := by
    simp only [KeccakfPermAir.extraction.inter_4995, KeccakfPermAir.extraction.inter_4994, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_4993 c row = (mc 937 + mc 1745 - mc 1316*mc 1745 - 2*mc 937*mc 1745 + 2*mc 937*mc 1316*mc 1745) + 2 * KeccakfPermAir.extraction.inter_4991 c row := by
    simp only [KeccakfPermAir.extraction.inter_4993, KeccakfPermAir.extraction.inter_4992, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_4991 c row = (mc 938 + mc 1746 - mc 1317*mc 1746 - 2*mc 938*mc 1746 + 2*mc 938*mc 1317*mc 1746) + 2 * KeccakfPermAir.extraction.inter_4989 c row := by
    simp only [KeccakfPermAir.extraction.inter_4991, KeccakfPermAir.extraction.inter_4990, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_4989 c row = (mc 939 + mc 1747 - mc 1318*mc 1747 - 2*mc 939*mc 1747 + 2*mc 939*mc 1318*mc 1747) + 2 * KeccakfPermAir.extraction.inter_4987 c row := by
    simp only [KeccakfPermAir.extraction.inter_4989, KeccakfPermAir.extraction.inter_4988, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_4987 c row = (mc 940 + mc 1748 - mc 1319*mc 1748 - 2*mc 940*mc 1748 + 2*mc 940*mc 1319*mc 1748) + 2 * KeccakfPermAir.extraction.inter_4985 c row := by
    simp only [KeccakfPermAir.extraction.inter_4987, KeccakfPermAir.extraction.inter_4986, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_4985 c row = (mc 941 + mc 1749 - mc 1320*mc 1749 - 2*mc 941*mc 1749 + 2*mc 941*mc 1320*mc 1749) + 2 * KeccakfPermAir.extraction.inter_4983 c row := by
    simp only [KeccakfPermAir.extraction.inter_4985, KeccakfPermAir.extraction.inter_4984, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_4983 c row = (mc 942 + mc 1750 - mc 1321*mc 1750 - 2*mc 942*mc 1750 + 2*mc 942*mc 1321*mc 1750) + 2 * KeccakfPermAir.extraction.inter_4981 c row := by
    simp only [KeccakfPermAir.extraction.inter_4983, KeccakfPermAir.extraction.inter_4982, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_4981 c row = (mc 943 + mc 1751 - mc 1322*mc 1751 - 2*mc 943*mc 1751 + 2*mc 943*mc 1322*mc 1751) := by
    simp only [KeccakfPermAir.extraction.inter_4981, KeccakfPermAir.extraction.inter_4980, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2951 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2951 c row) :
    ((mc 944 + mc 1752 - mc 1323*mc 1752 - 2*mc 944*mc 1752 + 2*mc 944*mc 1323*mc 1752) + 2*(mc 945 + mc 1753 - mc 1324*mc 1753 - 2*mc 945*mc 1753 + 2*mc 945*mc 1324*mc 1753) + 4*(mc 946 + mc 1754 - mc 1325*mc 1754 - 2*mc 946*mc 1754 + 2*mc 946*mc 1325*mc 1754) + 8*(mc 947 + mc 1755 - mc 1326*mc 1755 - 2*mc 947*mc 1755 + 2*mc 947*mc 1326*mc 1755) + 16*(mc 948 + mc 1756 - mc 1327*mc 1756 - 2*mc 948*mc 1756 + 2*mc 948*mc 1327*mc 1756) + 32*(mc 949 + mc 1757 - mc 1328*mc 1757 - 2*mc 949*mc 1757 + 2*mc 949*mc 1328*mc 1757) + 64*(mc 950 + mc 1758 - mc 1329*mc 1758 - 2*mc 950*mc 1758 + 2*mc 950*mc 1329*mc 1758) + 128*(mc 951 + mc 1759 - mc 1330*mc 1759 - 2*mc 951*mc 1759 + 2*mc 951*mc 1330*mc 1759) + 256*(mc 952 + mc 1760 - mc 1331*mc 1760 - 2*mc 952*mc 1760 + 2*mc 952*mc 1331*mc 1760) + 512*(mc 953 + mc 1697 - mc 1332*mc 1697 - 2*mc 953*mc 1697 + 2*mc 953*mc 1332*mc 1697) + 1024*(mc 954 + mc 1698 - mc 1333*mc 1698 - 2*mc 954*mc 1698 + 2*mc 954*mc 1333*mc 1698) + 2048*(mc 955 + mc 1699 - mc 1334*mc 1699 - 2*mc 955*mc 1699 + 2*mc 955*mc 1334*mc 1699) + 4096*(mc 956 + mc 1700 - mc 1335*mc 1700 - 2*mc 956*mc 1700 + 2*mc 956*mc 1335*mc 1700) + 8192*(mc 957 + mc 1701 - mc 1336*mc 1701 - 2*mc 957*mc 1701 + 2*mc 957*mc 1336*mc 1701) + 16384*(mc 958 + mc 1702 - mc 1337*mc 1702 - 2*mc 958*mc 1702 + 2*mc 958*mc 1337*mc 1702) + 32768*(mc 959 + mc 1703 - mc 1338*mc 1703 - 2*mc 959*mc 1703 + 2*mc 959*mc 1338*mc 1703)) - mc 2506 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2951, KeccakfPermAir.extraction.inter_5041, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5040 c row = (mc 945 + mc 1753 - mc 1324*mc 1753 - 2*mc 945*mc 1753 + 2*mc 945*mc 1324*mc 1753) + 2 * KeccakfPermAir.extraction.inter_5038 c row := by
    simp only [KeccakfPermAir.extraction.inter_5040, KeccakfPermAir.extraction.inter_5039, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5038 c row = (mc 946 + mc 1754 - mc 1325*mc 1754 - 2*mc 946*mc 1754 + 2*mc 946*mc 1325*mc 1754) + 2 * KeccakfPermAir.extraction.inter_5036 c row := by
    simp only [KeccakfPermAir.extraction.inter_5038, KeccakfPermAir.extraction.inter_5037, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5036 c row = (mc 947 + mc 1755 - mc 1326*mc 1755 - 2*mc 947*mc 1755 + 2*mc 947*mc 1326*mc 1755) + 2 * KeccakfPermAir.extraction.inter_5034 c row := by
    simp only [KeccakfPermAir.extraction.inter_5036, KeccakfPermAir.extraction.inter_5035, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5034 c row = (mc 948 + mc 1756 - mc 1327*mc 1756 - 2*mc 948*mc 1756 + 2*mc 948*mc 1327*mc 1756) + 2 * KeccakfPermAir.extraction.inter_5032 c row := by
    simp only [KeccakfPermAir.extraction.inter_5034, KeccakfPermAir.extraction.inter_5033, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5032 c row = (mc 949 + mc 1757 - mc 1328*mc 1757 - 2*mc 949*mc 1757 + 2*mc 949*mc 1328*mc 1757) + 2 * KeccakfPermAir.extraction.inter_5030 c row := by
    simp only [KeccakfPermAir.extraction.inter_5032, KeccakfPermAir.extraction.inter_5031, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5030 c row = (mc 950 + mc 1758 - mc 1329*mc 1758 - 2*mc 950*mc 1758 + 2*mc 950*mc 1329*mc 1758) + 2 * KeccakfPermAir.extraction.inter_5028 c row := by
    simp only [KeccakfPermAir.extraction.inter_5030, KeccakfPermAir.extraction.inter_5029, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5028 c row = (mc 951 + mc 1759 - mc 1330*mc 1759 - 2*mc 951*mc 1759 + 2*mc 951*mc 1330*mc 1759) + 2 * KeccakfPermAir.extraction.inter_5026 c row := by
    simp only [KeccakfPermAir.extraction.inter_5028, KeccakfPermAir.extraction.inter_5027, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5026 c row = (mc 952 + mc 1760 - mc 1331*mc 1760 - 2*mc 952*mc 1760 + 2*mc 952*mc 1331*mc 1760) + 2 * KeccakfPermAir.extraction.inter_5024 c row := by
    simp only [KeccakfPermAir.extraction.inter_5026, KeccakfPermAir.extraction.inter_5025, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5024 c row = (mc 953 + mc 1697 - mc 1332*mc 1697 - 2*mc 953*mc 1697 + 2*mc 953*mc 1332*mc 1697) + 2 * KeccakfPermAir.extraction.inter_5022 c row := by
    simp only [KeccakfPermAir.extraction.inter_5024, KeccakfPermAir.extraction.inter_5023, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5022 c row = (mc 954 + mc 1698 - mc 1333*mc 1698 - 2*mc 954*mc 1698 + 2*mc 954*mc 1333*mc 1698) + 2 * KeccakfPermAir.extraction.inter_5020 c row := by
    simp only [KeccakfPermAir.extraction.inter_5022, KeccakfPermAir.extraction.inter_5021, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5020 c row = (mc 955 + mc 1699 - mc 1334*mc 1699 - 2*mc 955*mc 1699 + 2*mc 955*mc 1334*mc 1699) + 2 * KeccakfPermAir.extraction.inter_5018 c row := by
    simp only [KeccakfPermAir.extraction.inter_5020, KeccakfPermAir.extraction.inter_5019, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5018 c row = (mc 956 + mc 1700 - mc 1335*mc 1700 - 2*mc 956*mc 1700 + 2*mc 956*mc 1335*mc 1700) + 2 * KeccakfPermAir.extraction.inter_5016 c row := by
    simp only [KeccakfPermAir.extraction.inter_5018, KeccakfPermAir.extraction.inter_5017, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5016 c row = (mc 957 + mc 1701 - mc 1336*mc 1701 - 2*mc 957*mc 1701 + 2*mc 957*mc 1336*mc 1701) + 2 * KeccakfPermAir.extraction.inter_5014 c row := by
    simp only [KeccakfPermAir.extraction.inter_5016, KeccakfPermAir.extraction.inter_5015, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5014 c row = (mc 958 + mc 1702 - mc 1337*mc 1702 - 2*mc 958*mc 1702 + 2*mc 958*mc 1337*mc 1702) + 2 * KeccakfPermAir.extraction.inter_5012 c row := by
    simp only [KeccakfPermAir.extraction.inter_5014, KeccakfPermAir.extraction.inter_5013, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5012 c row = (mc 959 + mc 1703 - mc 1338*mc 1703 - 2*mc 959*mc 1703 + 2*mc 959*mc 1338*mc 1703) := by
    simp only [KeccakfPermAir.extraction.inter_5012, KeccakfPermAir.extraction.inter_5011, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2952 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2952 c row) :
    ((mc 960 + mc 1704 - mc 1339*mc 1704 - 2*mc 960*mc 1704 + 2*mc 960*mc 1339*mc 1704) + 2*(mc 961 + mc 1705 - mc 1340*mc 1705 - 2*mc 961*mc 1705 + 2*mc 961*mc 1340*mc 1705) + 4*(mc 962 + mc 1706 - mc 1341*mc 1706 - 2*mc 962*mc 1706 + 2*mc 962*mc 1341*mc 1706) + 8*(mc 963 + mc 1707 - mc 1342*mc 1707 - 2*mc 963*mc 1707 + 2*mc 963*mc 1342*mc 1707) + 16*(mc 964 + mc 1708 - mc 1343*mc 1708 - 2*mc 964*mc 1708 + 2*mc 964*mc 1343*mc 1708) + 32*(mc 965 + mc 1709 - mc 1344*mc 1709 - 2*mc 965*mc 1709 + 2*mc 965*mc 1344*mc 1709) + 64*(mc 966 + mc 1710 - mc 1345*mc 1710 - 2*mc 966*mc 1710 + 2*mc 966*mc 1345*mc 1710) + 128*(mc 967 + mc 1711 - mc 1346*mc 1711 - 2*mc 967*mc 1711 + 2*mc 967*mc 1346*mc 1711) + 256*(mc 968 + mc 1712 - mc 1347*mc 1712 - 2*mc 968*mc 1712 + 2*mc 968*mc 1347*mc 1712) + 512*(mc 969 + mc 1713 - mc 1348*mc 1713 - 2*mc 969*mc 1713 + 2*mc 969*mc 1348*mc 1713) + 1024*(mc 970 + mc 1714 - mc 1349*mc 1714 - 2*mc 970*mc 1714 + 2*mc 970*mc 1349*mc 1714) + 2048*(mc 971 + mc 1715 - mc 1350*mc 1715 - 2*mc 971*mc 1715 + 2*mc 971*mc 1350*mc 1715) + 4096*(mc 972 + mc 1716 - mc 1351*mc 1716 - 2*mc 972*mc 1716 + 2*mc 972*mc 1351*mc 1716) + 8192*(mc 973 + mc 1717 - mc 1352*mc 1717 - 2*mc 973*mc 1717 + 2*mc 973*mc 1352*mc 1717) + 16384*(mc 974 + mc 1718 - mc 1353*mc 1718 - 2*mc 974*mc 1718 + 2*mc 974*mc 1353*mc 1718) + 32768*(mc 975 + mc 1719 - mc 1354*mc 1719 - 2*mc 975*mc 1719 + 2*mc 975*mc 1354*mc 1719)) - mc 2507 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2952, KeccakfPermAir.extraction.inter_5072, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5071 c row = (mc 961 + mc 1705 - mc 1340*mc 1705 - 2*mc 961*mc 1705 + 2*mc 961*mc 1340*mc 1705) + 2 * KeccakfPermAir.extraction.inter_5069 c row := by
    simp only [KeccakfPermAir.extraction.inter_5071, KeccakfPermAir.extraction.inter_5070, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5069 c row = (mc 962 + mc 1706 - mc 1341*mc 1706 - 2*mc 962*mc 1706 + 2*mc 962*mc 1341*mc 1706) + 2 * KeccakfPermAir.extraction.inter_5067 c row := by
    simp only [KeccakfPermAir.extraction.inter_5069, KeccakfPermAir.extraction.inter_5068, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5067 c row = (mc 963 + mc 1707 - mc 1342*mc 1707 - 2*mc 963*mc 1707 + 2*mc 963*mc 1342*mc 1707) + 2 * KeccakfPermAir.extraction.inter_5065 c row := by
    simp only [KeccakfPermAir.extraction.inter_5067, KeccakfPermAir.extraction.inter_5066, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5065 c row = (mc 964 + mc 1708 - mc 1343*mc 1708 - 2*mc 964*mc 1708 + 2*mc 964*mc 1343*mc 1708) + 2 * KeccakfPermAir.extraction.inter_5063 c row := by
    simp only [KeccakfPermAir.extraction.inter_5065, KeccakfPermAir.extraction.inter_5064, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5063 c row = (mc 965 + mc 1709 - mc 1344*mc 1709 - 2*mc 965*mc 1709 + 2*mc 965*mc 1344*mc 1709) + 2 * KeccakfPermAir.extraction.inter_5061 c row := by
    simp only [KeccakfPermAir.extraction.inter_5063, KeccakfPermAir.extraction.inter_5062, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5061 c row = (mc 966 + mc 1710 - mc 1345*mc 1710 - 2*mc 966*mc 1710 + 2*mc 966*mc 1345*mc 1710) + 2 * KeccakfPermAir.extraction.inter_5059 c row := by
    simp only [KeccakfPermAir.extraction.inter_5061, KeccakfPermAir.extraction.inter_5060, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5059 c row = (mc 967 + mc 1711 - mc 1346*mc 1711 - 2*mc 967*mc 1711 + 2*mc 967*mc 1346*mc 1711) + 2 * KeccakfPermAir.extraction.inter_5057 c row := by
    simp only [KeccakfPermAir.extraction.inter_5059, KeccakfPermAir.extraction.inter_5058, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5057 c row = (mc 968 + mc 1712 - mc 1347*mc 1712 - 2*mc 968*mc 1712 + 2*mc 968*mc 1347*mc 1712) + 2 * KeccakfPermAir.extraction.inter_5055 c row := by
    simp only [KeccakfPermAir.extraction.inter_5057, KeccakfPermAir.extraction.inter_5056, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5055 c row = (mc 969 + mc 1713 - mc 1348*mc 1713 - 2*mc 969*mc 1713 + 2*mc 969*mc 1348*mc 1713) + 2 * KeccakfPermAir.extraction.inter_5053 c row := by
    simp only [KeccakfPermAir.extraction.inter_5055, KeccakfPermAir.extraction.inter_5054, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5053 c row = (mc 970 + mc 1714 - mc 1349*mc 1714 - 2*mc 970*mc 1714 + 2*mc 970*mc 1349*mc 1714) + 2 * KeccakfPermAir.extraction.inter_5051 c row := by
    simp only [KeccakfPermAir.extraction.inter_5053, KeccakfPermAir.extraction.inter_5052, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5051 c row = (mc 971 + mc 1715 - mc 1350*mc 1715 - 2*mc 971*mc 1715 + 2*mc 971*mc 1350*mc 1715) + 2 * KeccakfPermAir.extraction.inter_5049 c row := by
    simp only [KeccakfPermAir.extraction.inter_5051, KeccakfPermAir.extraction.inter_5050, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5049 c row = (mc 972 + mc 1716 - mc 1351*mc 1716 - 2*mc 972*mc 1716 + 2*mc 972*mc 1351*mc 1716) + 2 * KeccakfPermAir.extraction.inter_5047 c row := by
    simp only [KeccakfPermAir.extraction.inter_5049, KeccakfPermAir.extraction.inter_5048, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5047 c row = (mc 973 + mc 1717 - mc 1352*mc 1717 - 2*mc 973*mc 1717 + 2*mc 973*mc 1352*mc 1717) + 2 * KeccakfPermAir.extraction.inter_5045 c row := by
    simp only [KeccakfPermAir.extraction.inter_5047, KeccakfPermAir.extraction.inter_5046, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5045 c row = (mc 974 + mc 1718 - mc 1353*mc 1718 - 2*mc 974*mc 1718 + 2*mc 974*mc 1353*mc 1718) + 2 * KeccakfPermAir.extraction.inter_5043 c row := by
    simp only [KeccakfPermAir.extraction.inter_5045, KeccakfPermAir.extraction.inter_5044, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5043 c row = (mc 975 + mc 1719 - mc 1354*mc 1719 - 2*mc 975*mc 1719 + 2*mc 975*mc 1354*mc 1719) := by
    simp only [KeccakfPermAir.extraction.inter_5043, KeccakfPermAir.extraction.inter_5042, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2953 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2953 c row) :
    ((mc 976 + mc 1720 - mc 1355*mc 1720 - 2*mc 976*mc 1720 + 2*mc 976*mc 1355*mc 1720) + 2*(mc 977 + mc 1721 - mc 1356*mc 1721 - 2*mc 977*mc 1721 + 2*mc 977*mc 1356*mc 1721) + 4*(mc 978 + mc 1722 - mc 1357*mc 1722 - 2*mc 978*mc 1722 + 2*mc 978*mc 1357*mc 1722) + 8*(mc 979 + mc 1723 - mc 1358*mc 1723 - 2*mc 979*mc 1723 + 2*mc 979*mc 1358*mc 1723) + 16*(mc 980 + mc 1724 - mc 1359*mc 1724 - 2*mc 980*mc 1724 + 2*mc 980*mc 1359*mc 1724) + 32*(mc 981 + mc 1725 - mc 1360*mc 1725 - 2*mc 981*mc 1725 + 2*mc 981*mc 1360*mc 1725) + 64*(mc 982 + mc 1726 - mc 1361*mc 1726 - 2*mc 982*mc 1726 + 2*mc 982*mc 1361*mc 1726) + 128*(mc 983 + mc 1727 - mc 1362*mc 1727 - 2*mc 983*mc 1727 + 2*mc 983*mc 1362*mc 1727) + 256*(mc 984 + mc 1728 - mc 1363*mc 1728 - 2*mc 984*mc 1728 + 2*mc 984*mc 1363*mc 1728) + 512*(mc 985 + mc 1729 - mc 1364*mc 1729 - 2*mc 985*mc 1729 + 2*mc 985*mc 1364*mc 1729) + 1024*(mc 986 + mc 1730 - mc 1365*mc 1730 - 2*mc 986*mc 1730 + 2*mc 986*mc 1365*mc 1730) + 2048*(mc 987 + mc 1731 - mc 1366*mc 1731 - 2*mc 987*mc 1731 + 2*mc 987*mc 1366*mc 1731) + 4096*(mc 988 + mc 1732 - mc 1367*mc 1732 - 2*mc 988*mc 1732 + 2*mc 988*mc 1367*mc 1732) + 8192*(mc 989 + mc 1733 - mc 1368*mc 1733 - 2*mc 989*mc 1733 + 2*mc 989*mc 1368*mc 1733) + 16384*(mc 990 + mc 1734 - mc 1369*mc 1734 - 2*mc 990*mc 1734 + 2*mc 990*mc 1369*mc 1734) + 32768*(mc 991 + mc 1735 - mc 1370*mc 1735 - 2*mc 991*mc 1735 + 2*mc 991*mc 1370*mc 1735)) - mc 2508 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2953, KeccakfPermAir.extraction.inter_5103, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5102 c row = (mc 977 + mc 1721 - mc 1356*mc 1721 - 2*mc 977*mc 1721 + 2*mc 977*mc 1356*mc 1721) + 2 * KeccakfPermAir.extraction.inter_5100 c row := by
    simp only [KeccakfPermAir.extraction.inter_5102, KeccakfPermAir.extraction.inter_5101, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5100 c row = (mc 978 + mc 1722 - mc 1357*mc 1722 - 2*mc 978*mc 1722 + 2*mc 978*mc 1357*mc 1722) + 2 * KeccakfPermAir.extraction.inter_5098 c row := by
    simp only [KeccakfPermAir.extraction.inter_5100, KeccakfPermAir.extraction.inter_5099, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5098 c row = (mc 979 + mc 1723 - mc 1358*mc 1723 - 2*mc 979*mc 1723 + 2*mc 979*mc 1358*mc 1723) + 2 * KeccakfPermAir.extraction.inter_5096 c row := by
    simp only [KeccakfPermAir.extraction.inter_5098, KeccakfPermAir.extraction.inter_5097, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5096 c row = (mc 980 + mc 1724 - mc 1359*mc 1724 - 2*mc 980*mc 1724 + 2*mc 980*mc 1359*mc 1724) + 2 * KeccakfPermAir.extraction.inter_5094 c row := by
    simp only [KeccakfPermAir.extraction.inter_5096, KeccakfPermAir.extraction.inter_5095, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5094 c row = (mc 981 + mc 1725 - mc 1360*mc 1725 - 2*mc 981*mc 1725 + 2*mc 981*mc 1360*mc 1725) + 2 * KeccakfPermAir.extraction.inter_5092 c row := by
    simp only [KeccakfPermAir.extraction.inter_5094, KeccakfPermAir.extraction.inter_5093, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5092 c row = (mc 982 + mc 1726 - mc 1361*mc 1726 - 2*mc 982*mc 1726 + 2*mc 982*mc 1361*mc 1726) + 2 * KeccakfPermAir.extraction.inter_5090 c row := by
    simp only [KeccakfPermAir.extraction.inter_5092, KeccakfPermAir.extraction.inter_5091, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5090 c row = (mc 983 + mc 1727 - mc 1362*mc 1727 - 2*mc 983*mc 1727 + 2*mc 983*mc 1362*mc 1727) + 2 * KeccakfPermAir.extraction.inter_5088 c row := by
    simp only [KeccakfPermAir.extraction.inter_5090, KeccakfPermAir.extraction.inter_5089, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5088 c row = (mc 984 + mc 1728 - mc 1363*mc 1728 - 2*mc 984*mc 1728 + 2*mc 984*mc 1363*mc 1728) + 2 * KeccakfPermAir.extraction.inter_5086 c row := by
    simp only [KeccakfPermAir.extraction.inter_5088, KeccakfPermAir.extraction.inter_5087, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5086 c row = (mc 985 + mc 1729 - mc 1364*mc 1729 - 2*mc 985*mc 1729 + 2*mc 985*mc 1364*mc 1729) + 2 * KeccakfPermAir.extraction.inter_5084 c row := by
    simp only [KeccakfPermAir.extraction.inter_5086, KeccakfPermAir.extraction.inter_5085, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5084 c row = (mc 986 + mc 1730 - mc 1365*mc 1730 - 2*mc 986*mc 1730 + 2*mc 986*mc 1365*mc 1730) + 2 * KeccakfPermAir.extraction.inter_5082 c row := by
    simp only [KeccakfPermAir.extraction.inter_5084, KeccakfPermAir.extraction.inter_5083, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5082 c row = (mc 987 + mc 1731 - mc 1366*mc 1731 - 2*mc 987*mc 1731 + 2*mc 987*mc 1366*mc 1731) + 2 * KeccakfPermAir.extraction.inter_5080 c row := by
    simp only [KeccakfPermAir.extraction.inter_5082, KeccakfPermAir.extraction.inter_5081, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5080 c row = (mc 988 + mc 1732 - mc 1367*mc 1732 - 2*mc 988*mc 1732 + 2*mc 988*mc 1367*mc 1732) + 2 * KeccakfPermAir.extraction.inter_5078 c row := by
    simp only [KeccakfPermAir.extraction.inter_5080, KeccakfPermAir.extraction.inter_5079, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5078 c row = (mc 989 + mc 1733 - mc 1368*mc 1733 - 2*mc 989*mc 1733 + 2*mc 989*mc 1368*mc 1733) + 2 * KeccakfPermAir.extraction.inter_5076 c row := by
    simp only [KeccakfPermAir.extraction.inter_5078, KeccakfPermAir.extraction.inter_5077, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5076 c row = (mc 990 + mc 1734 - mc 1369*mc 1734 - 2*mc 990*mc 1734 + 2*mc 990*mc 1369*mc 1734) + 2 * KeccakfPermAir.extraction.inter_5074 c row := by
    simp only [KeccakfPermAir.extraction.inter_5076, KeccakfPermAir.extraction.inter_5075, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5074 c row = (mc 991 + mc 1735 - mc 1370*mc 1735 - 2*mc 991*mc 1735 + 2*mc 991*mc 1370*mc 1735) := by
    simp only [KeccakfPermAir.extraction.inter_5074, KeccakfPermAir.extraction.inter_5073, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2954 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2954 c row) :
    ((mc 1371 + mc 2137 - mc 1736*mc 2137 - 2*mc 1371*mc 2137 + 2*mc 1371*mc 1736*mc 2137) + 2*(mc 1372 + mc 2138 - mc 1737*mc 2138 - 2*mc 1372*mc 2138 + 2*mc 1372*mc 1737*mc 2138) + 4*(mc 1373 + mc 2139 - mc 1738*mc 2139 - 2*mc 1373*mc 2139 + 2*mc 1373*mc 1738*mc 2139) + 8*(mc 1374 + mc 2140 - mc 1739*mc 2140 - 2*mc 1374*mc 2140 + 2*mc 1374*mc 1739*mc 2140) + 16*(mc 1375 + mc 2141 - mc 1740*mc 2141 - 2*mc 1375*mc 2141 + 2*mc 1375*mc 1740*mc 2141) + 32*(mc 1376 + mc 2142 - mc 1741*mc 2142 - 2*mc 1376*mc 2142 + 2*mc 1376*mc 1741*mc 2142) + 64*(mc 1313 + mc 2143 - mc 1742*mc 2143 - 2*mc 1313*mc 2143 + 2*mc 1313*mc 1742*mc 2143) + 128*(mc 1314 + mc 2144 - mc 1743*mc 2144 - 2*mc 1314*mc 2144 + 2*mc 1314*mc 1743*mc 2144) + 256*(mc 1315 + mc 2081 - mc 1744*mc 2081 - 2*mc 1315*mc 2081 + 2*mc 1315*mc 1744*mc 2081) + 512*(mc 1316 + mc 2082 - mc 1745*mc 2082 - 2*mc 1316*mc 2082 + 2*mc 1316*mc 1745*mc 2082) + 1024*(mc 1317 + mc 2083 - mc 1746*mc 2083 - 2*mc 1317*mc 2083 + 2*mc 1317*mc 1746*mc 2083) + 2048*(mc 1318 + mc 2084 - mc 1747*mc 2084 - 2*mc 1318*mc 2084 + 2*mc 1318*mc 1747*mc 2084) + 4096*(mc 1319 + mc 2085 - mc 1748*mc 2085 - 2*mc 1319*mc 2085 + 2*mc 1319*mc 1748*mc 2085) + 8192*(mc 1320 + mc 2086 - mc 1749*mc 2086 - 2*mc 1320*mc 2086 + 2*mc 1320*mc 1749*mc 2086) + 16384*(mc 1321 + mc 2087 - mc 1750*mc 2087 - 2*mc 1321*mc 2087 + 2*mc 1321*mc 1750*mc 2087) + 32768*(mc 1322 + mc 2088 - mc 1751*mc 2088 - 2*mc 1322*mc 2088 + 2*mc 1322*mc 1751*mc 2088)) - mc 2509 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2954, KeccakfPermAir.extraction.inter_5134, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5133 c row = (mc 1372 + mc 2138 - mc 1737*mc 2138 - 2*mc 1372*mc 2138 + 2*mc 1372*mc 1737*mc 2138) + 2 * KeccakfPermAir.extraction.inter_5131 c row := by
    simp only [KeccakfPermAir.extraction.inter_5133, KeccakfPermAir.extraction.inter_5132, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5131 c row = (mc 1373 + mc 2139 - mc 1738*mc 2139 - 2*mc 1373*mc 2139 + 2*mc 1373*mc 1738*mc 2139) + 2 * KeccakfPermAir.extraction.inter_5129 c row := by
    simp only [KeccakfPermAir.extraction.inter_5131, KeccakfPermAir.extraction.inter_5130, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5129 c row = (mc 1374 + mc 2140 - mc 1739*mc 2140 - 2*mc 1374*mc 2140 + 2*mc 1374*mc 1739*mc 2140) + 2 * KeccakfPermAir.extraction.inter_5127 c row := by
    simp only [KeccakfPermAir.extraction.inter_5129, KeccakfPermAir.extraction.inter_5128, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5127 c row = (mc 1375 + mc 2141 - mc 1740*mc 2141 - 2*mc 1375*mc 2141 + 2*mc 1375*mc 1740*mc 2141) + 2 * KeccakfPermAir.extraction.inter_5125 c row := by
    simp only [KeccakfPermAir.extraction.inter_5127, KeccakfPermAir.extraction.inter_5126, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5125 c row = (mc 1376 + mc 2142 - mc 1741*mc 2142 - 2*mc 1376*mc 2142 + 2*mc 1376*mc 1741*mc 2142) + 2 * KeccakfPermAir.extraction.inter_5123 c row := by
    simp only [KeccakfPermAir.extraction.inter_5125, KeccakfPermAir.extraction.inter_5124, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5123 c row = (mc 1313 + mc 2143 - mc 1742*mc 2143 - 2*mc 1313*mc 2143 + 2*mc 1313*mc 1742*mc 2143) + 2 * KeccakfPermAir.extraction.inter_5121 c row := by
    simp only [KeccakfPermAir.extraction.inter_5123, KeccakfPermAir.extraction.inter_5122, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5121 c row = (mc 1314 + mc 2144 - mc 1743*mc 2144 - 2*mc 1314*mc 2144 + 2*mc 1314*mc 1743*mc 2144) + 2 * KeccakfPermAir.extraction.inter_5119 c row := by
    simp only [KeccakfPermAir.extraction.inter_5121, KeccakfPermAir.extraction.inter_5120, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5119 c row = (mc 1315 + mc 2081 - mc 1744*mc 2081 - 2*mc 1315*mc 2081 + 2*mc 1315*mc 1744*mc 2081) + 2 * KeccakfPermAir.extraction.inter_5117 c row := by
    simp only [KeccakfPermAir.extraction.inter_5119, KeccakfPermAir.extraction.inter_5118, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5117 c row = (mc 1316 + mc 2082 - mc 1745*mc 2082 - 2*mc 1316*mc 2082 + 2*mc 1316*mc 1745*mc 2082) + 2 * KeccakfPermAir.extraction.inter_5115 c row := by
    simp only [KeccakfPermAir.extraction.inter_5117, KeccakfPermAir.extraction.inter_5116, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5115 c row = (mc 1317 + mc 2083 - mc 1746*mc 2083 - 2*mc 1317*mc 2083 + 2*mc 1317*mc 1746*mc 2083) + 2 * KeccakfPermAir.extraction.inter_5113 c row := by
    simp only [KeccakfPermAir.extraction.inter_5115, KeccakfPermAir.extraction.inter_5114, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5113 c row = (mc 1318 + mc 2084 - mc 1747*mc 2084 - 2*mc 1318*mc 2084 + 2*mc 1318*mc 1747*mc 2084) + 2 * KeccakfPermAir.extraction.inter_5111 c row := by
    simp only [KeccakfPermAir.extraction.inter_5113, KeccakfPermAir.extraction.inter_5112, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5111 c row = (mc 1319 + mc 2085 - mc 1748*mc 2085 - 2*mc 1319*mc 2085 + 2*mc 1319*mc 1748*mc 2085) + 2 * KeccakfPermAir.extraction.inter_5109 c row := by
    simp only [KeccakfPermAir.extraction.inter_5111, KeccakfPermAir.extraction.inter_5110, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5109 c row = (mc 1320 + mc 2086 - mc 1749*mc 2086 - 2*mc 1320*mc 2086 + 2*mc 1320*mc 1749*mc 2086) + 2 * KeccakfPermAir.extraction.inter_5107 c row := by
    simp only [KeccakfPermAir.extraction.inter_5109, KeccakfPermAir.extraction.inter_5108, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5107 c row = (mc 1321 + mc 2087 - mc 1750*mc 2087 - 2*mc 1321*mc 2087 + 2*mc 1321*mc 1750*mc 2087) + 2 * KeccakfPermAir.extraction.inter_5105 c row := by
    simp only [KeccakfPermAir.extraction.inter_5107, KeccakfPermAir.extraction.inter_5106, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5105 c row = (mc 1322 + mc 2088 - mc 1751*mc 2088 - 2*mc 1322*mc 2088 + 2*mc 1322*mc 1751*mc 2088) := by
    simp only [KeccakfPermAir.extraction.inter_5105, KeccakfPermAir.extraction.inter_5104, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2955 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2955 c row) :
    ((mc 1323 + mc 2089 - mc 1752*mc 2089 - 2*mc 1323*mc 2089 + 2*mc 1323*mc 1752*mc 2089) + 2*(mc 1324 + mc 2090 - mc 1753*mc 2090 - 2*mc 1324*mc 2090 + 2*mc 1324*mc 1753*mc 2090) + 4*(mc 1325 + mc 2091 - mc 1754*mc 2091 - 2*mc 1325*mc 2091 + 2*mc 1325*mc 1754*mc 2091) + 8*(mc 1326 + mc 2092 - mc 1755*mc 2092 - 2*mc 1326*mc 2092 + 2*mc 1326*mc 1755*mc 2092) + 16*(mc 1327 + mc 2093 - mc 1756*mc 2093 - 2*mc 1327*mc 2093 + 2*mc 1327*mc 1756*mc 2093) + 32*(mc 1328 + mc 2094 - mc 1757*mc 2094 - 2*mc 1328*mc 2094 + 2*mc 1328*mc 1757*mc 2094) + 64*(mc 1329 + mc 2095 - mc 1758*mc 2095 - 2*mc 1329*mc 2095 + 2*mc 1329*mc 1758*mc 2095) + 128*(mc 1330 + mc 2096 - mc 1759*mc 2096 - 2*mc 1330*mc 2096 + 2*mc 1330*mc 1759*mc 2096) + 256*(mc 1331 + mc 2097 - mc 1760*mc 2097 - 2*mc 1331*mc 2097 + 2*mc 1331*mc 1760*mc 2097) + 512*(mc 1332 + mc 2098 - mc 1697*mc 2098 - 2*mc 1332*mc 2098 + 2*mc 1332*mc 1697*mc 2098) + 1024*(mc 1333 + mc 2099 - mc 1698*mc 2099 - 2*mc 1333*mc 2099 + 2*mc 1333*mc 1698*mc 2099) + 2048*(mc 1334 + mc 2100 - mc 1699*mc 2100 - 2*mc 1334*mc 2100 + 2*mc 1334*mc 1699*mc 2100) + 4096*(mc 1335 + mc 2101 - mc 1700*mc 2101 - 2*mc 1335*mc 2101 + 2*mc 1335*mc 1700*mc 2101) + 8192*(mc 1336 + mc 2102 - mc 1701*mc 2102 - 2*mc 1336*mc 2102 + 2*mc 1336*mc 1701*mc 2102) + 16384*(mc 1337 + mc 2103 - mc 1702*mc 2103 - 2*mc 1337*mc 2103 + 2*mc 1337*mc 1702*mc 2103) + 32768*(mc 1338 + mc 2104 - mc 1703*mc 2104 - 2*mc 1338*mc 2104 + 2*mc 1338*mc 1703*mc 2104)) - mc 2510 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2955, KeccakfPermAir.extraction.inter_5165, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5164 c row = (mc 1324 + mc 2090 - mc 1753*mc 2090 - 2*mc 1324*mc 2090 + 2*mc 1324*mc 1753*mc 2090) + 2 * KeccakfPermAir.extraction.inter_5162 c row := by
    simp only [KeccakfPermAir.extraction.inter_5164, KeccakfPermAir.extraction.inter_5163, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5162 c row = (mc 1325 + mc 2091 - mc 1754*mc 2091 - 2*mc 1325*mc 2091 + 2*mc 1325*mc 1754*mc 2091) + 2 * KeccakfPermAir.extraction.inter_5160 c row := by
    simp only [KeccakfPermAir.extraction.inter_5162, KeccakfPermAir.extraction.inter_5161, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5160 c row = (mc 1326 + mc 2092 - mc 1755*mc 2092 - 2*mc 1326*mc 2092 + 2*mc 1326*mc 1755*mc 2092) + 2 * KeccakfPermAir.extraction.inter_5158 c row := by
    simp only [KeccakfPermAir.extraction.inter_5160, KeccakfPermAir.extraction.inter_5159, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5158 c row = (mc 1327 + mc 2093 - mc 1756*mc 2093 - 2*mc 1327*mc 2093 + 2*mc 1327*mc 1756*mc 2093) + 2 * KeccakfPermAir.extraction.inter_5156 c row := by
    simp only [KeccakfPermAir.extraction.inter_5158, KeccakfPermAir.extraction.inter_5157, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5156 c row = (mc 1328 + mc 2094 - mc 1757*mc 2094 - 2*mc 1328*mc 2094 + 2*mc 1328*mc 1757*mc 2094) + 2 * KeccakfPermAir.extraction.inter_5154 c row := by
    simp only [KeccakfPermAir.extraction.inter_5156, KeccakfPermAir.extraction.inter_5155, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5154 c row = (mc 1329 + mc 2095 - mc 1758*mc 2095 - 2*mc 1329*mc 2095 + 2*mc 1329*mc 1758*mc 2095) + 2 * KeccakfPermAir.extraction.inter_5152 c row := by
    simp only [KeccakfPermAir.extraction.inter_5154, KeccakfPermAir.extraction.inter_5153, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5152 c row = (mc 1330 + mc 2096 - mc 1759*mc 2096 - 2*mc 1330*mc 2096 + 2*mc 1330*mc 1759*mc 2096) + 2 * KeccakfPermAir.extraction.inter_5150 c row := by
    simp only [KeccakfPermAir.extraction.inter_5152, KeccakfPermAir.extraction.inter_5151, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5150 c row = (mc 1331 + mc 2097 - mc 1760*mc 2097 - 2*mc 1331*mc 2097 + 2*mc 1331*mc 1760*mc 2097) + 2 * KeccakfPermAir.extraction.inter_5148 c row := by
    simp only [KeccakfPermAir.extraction.inter_5150, KeccakfPermAir.extraction.inter_5149, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5148 c row = (mc 1332 + mc 2098 - mc 1697*mc 2098 - 2*mc 1332*mc 2098 + 2*mc 1332*mc 1697*mc 2098) + 2 * KeccakfPermAir.extraction.inter_5146 c row := by
    simp only [KeccakfPermAir.extraction.inter_5148, KeccakfPermAir.extraction.inter_5147, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5146 c row = (mc 1333 + mc 2099 - mc 1698*mc 2099 - 2*mc 1333*mc 2099 + 2*mc 1333*mc 1698*mc 2099) + 2 * KeccakfPermAir.extraction.inter_5144 c row := by
    simp only [KeccakfPermAir.extraction.inter_5146, KeccakfPermAir.extraction.inter_5145, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5144 c row = (mc 1334 + mc 2100 - mc 1699*mc 2100 - 2*mc 1334*mc 2100 + 2*mc 1334*mc 1699*mc 2100) + 2 * KeccakfPermAir.extraction.inter_5142 c row := by
    simp only [KeccakfPermAir.extraction.inter_5144, KeccakfPermAir.extraction.inter_5143, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5142 c row = (mc 1335 + mc 2101 - mc 1700*mc 2101 - 2*mc 1335*mc 2101 + 2*mc 1335*mc 1700*mc 2101) + 2 * KeccakfPermAir.extraction.inter_5140 c row := by
    simp only [KeccakfPermAir.extraction.inter_5142, KeccakfPermAir.extraction.inter_5141, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5140 c row = (mc 1336 + mc 2102 - mc 1701*mc 2102 - 2*mc 1336*mc 2102 + 2*mc 1336*mc 1701*mc 2102) + 2 * KeccakfPermAir.extraction.inter_5138 c row := by
    simp only [KeccakfPermAir.extraction.inter_5140, KeccakfPermAir.extraction.inter_5139, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5138 c row = (mc 1337 + mc 2103 - mc 1702*mc 2103 - 2*mc 1337*mc 2103 + 2*mc 1337*mc 1702*mc 2103) + 2 * KeccakfPermAir.extraction.inter_5136 c row := by
    simp only [KeccakfPermAir.extraction.inter_5138, KeccakfPermAir.extraction.inter_5137, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5136 c row = (mc 1338 + mc 2104 - mc 1703*mc 2104 - 2*mc 1338*mc 2104 + 2*mc 1338*mc 1703*mc 2104) := by
    simp only [KeccakfPermAir.extraction.inter_5136, KeccakfPermAir.extraction.inter_5135, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2956 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2956 c row) :
    ((mc 1339 + mc 2105 - mc 1704*mc 2105 - 2*mc 1339*mc 2105 + 2*mc 1339*mc 1704*mc 2105) + 2*(mc 1340 + mc 2106 - mc 1705*mc 2106 - 2*mc 1340*mc 2106 + 2*mc 1340*mc 1705*mc 2106) + 4*(mc 1341 + mc 2107 - mc 1706*mc 2107 - 2*mc 1341*mc 2107 + 2*mc 1341*mc 1706*mc 2107) + 8*(mc 1342 + mc 2108 - mc 1707*mc 2108 - 2*mc 1342*mc 2108 + 2*mc 1342*mc 1707*mc 2108) + 16*(mc 1343 + mc 2109 - mc 1708*mc 2109 - 2*mc 1343*mc 2109 + 2*mc 1343*mc 1708*mc 2109) + 32*(mc 1344 + mc 2110 - mc 1709*mc 2110 - 2*mc 1344*mc 2110 + 2*mc 1344*mc 1709*mc 2110) + 64*(mc 1345 + mc 2111 - mc 1710*mc 2111 - 2*mc 1345*mc 2111 + 2*mc 1345*mc 1710*mc 2111) + 128*(mc 1346 + mc 2112 - mc 1711*mc 2112 - 2*mc 1346*mc 2112 + 2*mc 1346*mc 1711*mc 2112) + 256*(mc 1347 + mc 2113 - mc 1712*mc 2113 - 2*mc 1347*mc 2113 + 2*mc 1347*mc 1712*mc 2113) + 512*(mc 1348 + mc 2114 - mc 1713*mc 2114 - 2*mc 1348*mc 2114 + 2*mc 1348*mc 1713*mc 2114) + 1024*(mc 1349 + mc 2115 - mc 1714*mc 2115 - 2*mc 1349*mc 2115 + 2*mc 1349*mc 1714*mc 2115) + 2048*(mc 1350 + mc 2116 - mc 1715*mc 2116 - 2*mc 1350*mc 2116 + 2*mc 1350*mc 1715*mc 2116) + 4096*(mc 1351 + mc 2117 - mc 1716*mc 2117 - 2*mc 1351*mc 2117 + 2*mc 1351*mc 1716*mc 2117) + 8192*(mc 1352 + mc 2118 - mc 1717*mc 2118 - 2*mc 1352*mc 2118 + 2*mc 1352*mc 1717*mc 2118) + 16384*(mc 1353 + mc 2119 - mc 1718*mc 2119 - 2*mc 1353*mc 2119 + 2*mc 1353*mc 1718*mc 2119) + 32768*(mc 1354 + mc 2120 - mc 1719*mc 2120 - 2*mc 1354*mc 2120 + 2*mc 1354*mc 1719*mc 2120)) - mc 2511 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2956, KeccakfPermAir.extraction.inter_5196, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5195 c row = (mc 1340 + mc 2106 - mc 1705*mc 2106 - 2*mc 1340*mc 2106 + 2*mc 1340*mc 1705*mc 2106) + 2 * KeccakfPermAir.extraction.inter_5193 c row := by
    simp only [KeccakfPermAir.extraction.inter_5195, KeccakfPermAir.extraction.inter_5194, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5193 c row = (mc 1341 + mc 2107 - mc 1706*mc 2107 - 2*mc 1341*mc 2107 + 2*mc 1341*mc 1706*mc 2107) + 2 * KeccakfPermAir.extraction.inter_5191 c row := by
    simp only [KeccakfPermAir.extraction.inter_5193, KeccakfPermAir.extraction.inter_5192, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5191 c row = (mc 1342 + mc 2108 - mc 1707*mc 2108 - 2*mc 1342*mc 2108 + 2*mc 1342*mc 1707*mc 2108) + 2 * KeccakfPermAir.extraction.inter_5189 c row := by
    simp only [KeccakfPermAir.extraction.inter_5191, KeccakfPermAir.extraction.inter_5190, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5189 c row = (mc 1343 + mc 2109 - mc 1708*mc 2109 - 2*mc 1343*mc 2109 + 2*mc 1343*mc 1708*mc 2109) + 2 * KeccakfPermAir.extraction.inter_5187 c row := by
    simp only [KeccakfPermAir.extraction.inter_5189, KeccakfPermAir.extraction.inter_5188, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5187 c row = (mc 1344 + mc 2110 - mc 1709*mc 2110 - 2*mc 1344*mc 2110 + 2*mc 1344*mc 1709*mc 2110) + 2 * KeccakfPermAir.extraction.inter_5185 c row := by
    simp only [KeccakfPermAir.extraction.inter_5187, KeccakfPermAir.extraction.inter_5186, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5185 c row = (mc 1345 + mc 2111 - mc 1710*mc 2111 - 2*mc 1345*mc 2111 + 2*mc 1345*mc 1710*mc 2111) + 2 * KeccakfPermAir.extraction.inter_5183 c row := by
    simp only [KeccakfPermAir.extraction.inter_5185, KeccakfPermAir.extraction.inter_5184, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5183 c row = (mc 1346 + mc 2112 - mc 1711*mc 2112 - 2*mc 1346*mc 2112 + 2*mc 1346*mc 1711*mc 2112) + 2 * KeccakfPermAir.extraction.inter_5181 c row := by
    simp only [KeccakfPermAir.extraction.inter_5183, KeccakfPermAir.extraction.inter_5182, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5181 c row = (mc 1347 + mc 2113 - mc 1712*mc 2113 - 2*mc 1347*mc 2113 + 2*mc 1347*mc 1712*mc 2113) + 2 * KeccakfPermAir.extraction.inter_5179 c row := by
    simp only [KeccakfPermAir.extraction.inter_5181, KeccakfPermAir.extraction.inter_5180, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5179 c row = (mc 1348 + mc 2114 - mc 1713*mc 2114 - 2*mc 1348*mc 2114 + 2*mc 1348*mc 1713*mc 2114) + 2 * KeccakfPermAir.extraction.inter_5177 c row := by
    simp only [KeccakfPermAir.extraction.inter_5179, KeccakfPermAir.extraction.inter_5178, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5177 c row = (mc 1349 + mc 2115 - mc 1714*mc 2115 - 2*mc 1349*mc 2115 + 2*mc 1349*mc 1714*mc 2115) + 2 * KeccakfPermAir.extraction.inter_5175 c row := by
    simp only [KeccakfPermAir.extraction.inter_5177, KeccakfPermAir.extraction.inter_5176, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5175 c row = (mc 1350 + mc 2116 - mc 1715*mc 2116 - 2*mc 1350*mc 2116 + 2*mc 1350*mc 1715*mc 2116) + 2 * KeccakfPermAir.extraction.inter_5173 c row := by
    simp only [KeccakfPermAir.extraction.inter_5175, KeccakfPermAir.extraction.inter_5174, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5173 c row = (mc 1351 + mc 2117 - mc 1716*mc 2117 - 2*mc 1351*mc 2117 + 2*mc 1351*mc 1716*mc 2117) + 2 * KeccakfPermAir.extraction.inter_5171 c row := by
    simp only [KeccakfPermAir.extraction.inter_5173, KeccakfPermAir.extraction.inter_5172, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5171 c row = (mc 1352 + mc 2118 - mc 1717*mc 2118 - 2*mc 1352*mc 2118 + 2*mc 1352*mc 1717*mc 2118) + 2 * KeccakfPermAir.extraction.inter_5169 c row := by
    simp only [KeccakfPermAir.extraction.inter_5171, KeccakfPermAir.extraction.inter_5170, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5169 c row = (mc 1353 + mc 2119 - mc 1718*mc 2119 - 2*mc 1353*mc 2119 + 2*mc 1353*mc 1718*mc 2119) + 2 * KeccakfPermAir.extraction.inter_5167 c row := by
    simp only [KeccakfPermAir.extraction.inter_5169, KeccakfPermAir.extraction.inter_5168, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5167 c row = (mc 1354 + mc 2120 - mc 1719*mc 2120 - 2*mc 1354*mc 2120 + 2*mc 1354*mc 1719*mc 2120) := by
    simp only [KeccakfPermAir.extraction.inter_5167, KeccakfPermAir.extraction.inter_5166, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2957 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2957 c row) :
    ((mc 1355 + mc 2121 - mc 1720*mc 2121 - 2*mc 1355*mc 2121 + 2*mc 1355*mc 1720*mc 2121) + 2*(mc 1356 + mc 2122 - mc 1721*mc 2122 - 2*mc 1356*mc 2122 + 2*mc 1356*mc 1721*mc 2122) + 4*(mc 1357 + mc 2123 - mc 1722*mc 2123 - 2*mc 1357*mc 2123 + 2*mc 1357*mc 1722*mc 2123) + 8*(mc 1358 + mc 2124 - mc 1723*mc 2124 - 2*mc 1358*mc 2124 + 2*mc 1358*mc 1723*mc 2124) + 16*(mc 1359 + mc 2125 - mc 1724*mc 2125 - 2*mc 1359*mc 2125 + 2*mc 1359*mc 1724*mc 2125) + 32*(mc 1360 + mc 2126 - mc 1725*mc 2126 - 2*mc 1360*mc 2126 + 2*mc 1360*mc 1725*mc 2126) + 64*(mc 1361 + mc 2127 - mc 1726*mc 2127 - 2*mc 1361*mc 2127 + 2*mc 1361*mc 1726*mc 2127) + 128*(mc 1362 + mc 2128 - mc 1727*mc 2128 - 2*mc 1362*mc 2128 + 2*mc 1362*mc 1727*mc 2128) + 256*(mc 1363 + mc 2129 - mc 1728*mc 2129 - 2*mc 1363*mc 2129 + 2*mc 1363*mc 1728*mc 2129) + 512*(mc 1364 + mc 2130 - mc 1729*mc 2130 - 2*mc 1364*mc 2130 + 2*mc 1364*mc 1729*mc 2130) + 1024*(mc 1365 + mc 2131 - mc 1730*mc 2131 - 2*mc 1365*mc 2131 + 2*mc 1365*mc 1730*mc 2131) + 2048*(mc 1366 + mc 2132 - mc 1731*mc 2132 - 2*mc 1366*mc 2132 + 2*mc 1366*mc 1731*mc 2132) + 4096*(mc 1367 + mc 2133 - mc 1732*mc 2133 - 2*mc 1367*mc 2133 + 2*mc 1367*mc 1732*mc 2133) + 8192*(mc 1368 + mc 2134 - mc 1733*mc 2134 - 2*mc 1368*mc 2134 + 2*mc 1368*mc 1733*mc 2134) + 16384*(mc 1369 + mc 2135 - mc 1734*mc 2135 - 2*mc 1369*mc 2135 + 2*mc 1369*mc 1734*mc 2135) + 32768*(mc 1370 + mc 2136 - mc 1735*mc 2136 - 2*mc 1370*mc 2136 + 2*mc 1370*mc 1735*mc 2136)) - mc 2512 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2957, KeccakfPermAir.extraction.inter_5227, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5226 c row = (mc 1356 + mc 2122 - mc 1721*mc 2122 - 2*mc 1356*mc 2122 + 2*mc 1356*mc 1721*mc 2122) + 2 * KeccakfPermAir.extraction.inter_5224 c row := by
    simp only [KeccakfPermAir.extraction.inter_5226, KeccakfPermAir.extraction.inter_5225, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5224 c row = (mc 1357 + mc 2123 - mc 1722*mc 2123 - 2*mc 1357*mc 2123 + 2*mc 1357*mc 1722*mc 2123) + 2 * KeccakfPermAir.extraction.inter_5222 c row := by
    simp only [KeccakfPermAir.extraction.inter_5224, KeccakfPermAir.extraction.inter_5223, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5222 c row = (mc 1358 + mc 2124 - mc 1723*mc 2124 - 2*mc 1358*mc 2124 + 2*mc 1358*mc 1723*mc 2124) + 2 * KeccakfPermAir.extraction.inter_5220 c row := by
    simp only [KeccakfPermAir.extraction.inter_5222, KeccakfPermAir.extraction.inter_5221, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5220 c row = (mc 1359 + mc 2125 - mc 1724*mc 2125 - 2*mc 1359*mc 2125 + 2*mc 1359*mc 1724*mc 2125) + 2 * KeccakfPermAir.extraction.inter_5218 c row := by
    simp only [KeccakfPermAir.extraction.inter_5220, KeccakfPermAir.extraction.inter_5219, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5218 c row = (mc 1360 + mc 2126 - mc 1725*mc 2126 - 2*mc 1360*mc 2126 + 2*mc 1360*mc 1725*mc 2126) + 2 * KeccakfPermAir.extraction.inter_5216 c row := by
    simp only [KeccakfPermAir.extraction.inter_5218, KeccakfPermAir.extraction.inter_5217, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5216 c row = (mc 1361 + mc 2127 - mc 1726*mc 2127 - 2*mc 1361*mc 2127 + 2*mc 1361*mc 1726*mc 2127) + 2 * KeccakfPermAir.extraction.inter_5214 c row := by
    simp only [KeccakfPermAir.extraction.inter_5216, KeccakfPermAir.extraction.inter_5215, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5214 c row = (mc 1362 + mc 2128 - mc 1727*mc 2128 - 2*mc 1362*mc 2128 + 2*mc 1362*mc 1727*mc 2128) + 2 * KeccakfPermAir.extraction.inter_5212 c row := by
    simp only [KeccakfPermAir.extraction.inter_5214, KeccakfPermAir.extraction.inter_5213, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5212 c row = (mc 1363 + mc 2129 - mc 1728*mc 2129 - 2*mc 1363*mc 2129 + 2*mc 1363*mc 1728*mc 2129) + 2 * KeccakfPermAir.extraction.inter_5210 c row := by
    simp only [KeccakfPermAir.extraction.inter_5212, KeccakfPermAir.extraction.inter_5211, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5210 c row = (mc 1364 + mc 2130 - mc 1729*mc 2130 - 2*mc 1364*mc 2130 + 2*mc 1364*mc 1729*mc 2130) + 2 * KeccakfPermAir.extraction.inter_5208 c row := by
    simp only [KeccakfPermAir.extraction.inter_5210, KeccakfPermAir.extraction.inter_5209, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5208 c row = (mc 1365 + mc 2131 - mc 1730*mc 2131 - 2*mc 1365*mc 2131 + 2*mc 1365*mc 1730*mc 2131) + 2 * KeccakfPermAir.extraction.inter_5206 c row := by
    simp only [KeccakfPermAir.extraction.inter_5208, KeccakfPermAir.extraction.inter_5207, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5206 c row = (mc 1366 + mc 2132 - mc 1731*mc 2132 - 2*mc 1366*mc 2132 + 2*mc 1366*mc 1731*mc 2132) + 2 * KeccakfPermAir.extraction.inter_5204 c row := by
    simp only [KeccakfPermAir.extraction.inter_5206, KeccakfPermAir.extraction.inter_5205, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5204 c row = (mc 1367 + mc 2133 - mc 1732*mc 2133 - 2*mc 1367*mc 2133 + 2*mc 1367*mc 1732*mc 2133) + 2 * KeccakfPermAir.extraction.inter_5202 c row := by
    simp only [KeccakfPermAir.extraction.inter_5204, KeccakfPermAir.extraction.inter_5203, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5202 c row = (mc 1368 + mc 2134 - mc 1733*mc 2134 - 2*mc 1368*mc 2134 + 2*mc 1368*mc 1733*mc 2134) + 2 * KeccakfPermAir.extraction.inter_5200 c row := by
    simp only [KeccakfPermAir.extraction.inter_5202, KeccakfPermAir.extraction.inter_5201, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5200 c row = (mc 1369 + mc 2135 - mc 1734*mc 2135 - 2*mc 1369*mc 2135 + 2*mc 1369*mc 1734*mc 2135) + 2 * KeccakfPermAir.extraction.inter_5198 c row := by
    simp only [KeccakfPermAir.extraction.inter_5200, KeccakfPermAir.extraction.inter_5199, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5198 c row = (mc 1370 + mc 2136 - mc 1735*mc 2136 - 2*mc 1370*mc 2136 + 2*mc 1370*mc 1735*mc 2136) := by
    simp only [KeccakfPermAir.extraction.inter_5198, KeccakfPermAir.extraction.inter_5197, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2958 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2958 c row) :
    ((mc 1736 + mc 2191 - mc 2137*mc 2191 - 2*mc 1736*mc 2191 + 2*mc 1736*mc 2137*mc 2191) + 2*(mc 1737 + mc 2192 - mc 2138*mc 2192 - 2*mc 1737*mc 2192 + 2*mc 1737*mc 2138*mc 2192) + 4*(mc 1738 + mc 2193 - mc 2139*mc 2193 - 2*mc 1738*mc 2193 + 2*mc 1738*mc 2139*mc 2193) + 8*(mc 1739 + mc 2194 - mc 2140*mc 2194 - 2*mc 1739*mc 2194 + 2*mc 1739*mc 2140*mc 2194) + 16*(mc 1740 + mc 2195 - mc 2141*mc 2195 - 2*mc 1740*mc 2195 + 2*mc 1740*mc 2141*mc 2195) + 32*(mc 1741 + mc 2196 - mc 2142*mc 2196 - 2*mc 1741*mc 2196 + 2*mc 1741*mc 2142*mc 2196) + 64*(mc 1742 + mc 2197 - mc 2143*mc 2197 - 2*mc 1742*mc 2197 + 2*mc 1742*mc 2143*mc 2197) + 128*(mc 1743 + mc 2198 - mc 2144*mc 2198 - 2*mc 1743*mc 2198 + 2*mc 1743*mc 2144*mc 2198) + 256*(mc 1744 + mc 2199 - mc 2081*mc 2199 - 2*mc 1744*mc 2199 + 2*mc 1744*mc 2081*mc 2199) + 512*(mc 1745 + mc 2200 - mc 2082*mc 2200 - 2*mc 1745*mc 2200 + 2*mc 1745*mc 2082*mc 2200) + 1024*(mc 1746 + mc 2201 - mc 2083*mc 2201 - 2*mc 1746*mc 2201 + 2*mc 1746*mc 2083*mc 2201) + 2048*(mc 1747 + mc 2202 - mc 2084*mc 2202 - 2*mc 1747*mc 2202 + 2*mc 1747*mc 2084*mc 2202) + 4096*(mc 1748 + mc 2203 - mc 2085*mc 2203 - 2*mc 1748*mc 2203 + 2*mc 1748*mc 2085*mc 2203) + 8192*(mc 1749 + mc 2204 - mc 2086*mc 2204 - 2*mc 1749*mc 2204 + 2*mc 1749*mc 2086*mc 2204) + 16384*(mc 1750 + mc 2205 - mc 2087*mc 2205 - 2*mc 1750*mc 2205 + 2*mc 1750*mc 2087*mc 2205) + 32768*(mc 1751 + mc 2206 - mc 2088*mc 2206 - 2*mc 1751*mc 2206 + 2*mc 1751*mc 2088*mc 2206)) - mc 2513 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2958, KeccakfPermAir.extraction.inter_5258, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5257 c row = (mc 1737 + mc 2192 - mc 2138*mc 2192 - 2*mc 1737*mc 2192 + 2*mc 1737*mc 2138*mc 2192) + 2 * KeccakfPermAir.extraction.inter_5255 c row := by
    simp only [KeccakfPermAir.extraction.inter_5257, KeccakfPermAir.extraction.inter_5256, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5255 c row = (mc 1738 + mc 2193 - mc 2139*mc 2193 - 2*mc 1738*mc 2193 + 2*mc 1738*mc 2139*mc 2193) + 2 * KeccakfPermAir.extraction.inter_5253 c row := by
    simp only [KeccakfPermAir.extraction.inter_5255, KeccakfPermAir.extraction.inter_5254, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5253 c row = (mc 1739 + mc 2194 - mc 2140*mc 2194 - 2*mc 1739*mc 2194 + 2*mc 1739*mc 2140*mc 2194) + 2 * KeccakfPermAir.extraction.inter_5251 c row := by
    simp only [KeccakfPermAir.extraction.inter_5253, KeccakfPermAir.extraction.inter_5252, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5251 c row = (mc 1740 + mc 2195 - mc 2141*mc 2195 - 2*mc 1740*mc 2195 + 2*mc 1740*mc 2141*mc 2195) + 2 * KeccakfPermAir.extraction.inter_5249 c row := by
    simp only [KeccakfPermAir.extraction.inter_5251, KeccakfPermAir.extraction.inter_5250, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5249 c row = (mc 1741 + mc 2196 - mc 2142*mc 2196 - 2*mc 1741*mc 2196 + 2*mc 1741*mc 2142*mc 2196) + 2 * KeccakfPermAir.extraction.inter_5247 c row := by
    simp only [KeccakfPermAir.extraction.inter_5249, KeccakfPermAir.extraction.inter_5248, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5247 c row = (mc 1742 + mc 2197 - mc 2143*mc 2197 - 2*mc 1742*mc 2197 + 2*mc 1742*mc 2143*mc 2197) + 2 * KeccakfPermAir.extraction.inter_5245 c row := by
    simp only [KeccakfPermAir.extraction.inter_5247, KeccakfPermAir.extraction.inter_5246, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5245 c row = (mc 1743 + mc 2198 - mc 2144*mc 2198 - 2*mc 1743*mc 2198 + 2*mc 1743*mc 2144*mc 2198) + 2 * KeccakfPermAir.extraction.inter_5243 c row := by
    simp only [KeccakfPermAir.extraction.inter_5245, KeccakfPermAir.extraction.inter_5244, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5243 c row = (mc 1744 + mc 2199 - mc 2081*mc 2199 - 2*mc 1744*mc 2199 + 2*mc 1744*mc 2081*mc 2199) + 2 * KeccakfPermAir.extraction.inter_5241 c row := by
    simp only [KeccakfPermAir.extraction.inter_5243, KeccakfPermAir.extraction.inter_5242, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5241 c row = (mc 1745 + mc 2200 - mc 2082*mc 2200 - 2*mc 1745*mc 2200 + 2*mc 1745*mc 2082*mc 2200) + 2 * KeccakfPermAir.extraction.inter_5239 c row := by
    simp only [KeccakfPermAir.extraction.inter_5241, KeccakfPermAir.extraction.inter_5240, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5239 c row = (mc 1746 + mc 2201 - mc 2083*mc 2201 - 2*mc 1746*mc 2201 + 2*mc 1746*mc 2083*mc 2201) + 2 * KeccakfPermAir.extraction.inter_5237 c row := by
    simp only [KeccakfPermAir.extraction.inter_5239, KeccakfPermAir.extraction.inter_5238, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5237 c row = (mc 1747 + mc 2202 - mc 2084*mc 2202 - 2*mc 1747*mc 2202 + 2*mc 1747*mc 2084*mc 2202) + 2 * KeccakfPermAir.extraction.inter_5235 c row := by
    simp only [KeccakfPermAir.extraction.inter_5237, KeccakfPermAir.extraction.inter_5236, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5235 c row = (mc 1748 + mc 2203 - mc 2085*mc 2203 - 2*mc 1748*mc 2203 + 2*mc 1748*mc 2085*mc 2203) + 2 * KeccakfPermAir.extraction.inter_5233 c row := by
    simp only [KeccakfPermAir.extraction.inter_5235, KeccakfPermAir.extraction.inter_5234, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5233 c row = (mc 1749 + mc 2204 - mc 2086*mc 2204 - 2*mc 1749*mc 2204 + 2*mc 1749*mc 2086*mc 2204) + 2 * KeccakfPermAir.extraction.inter_5231 c row := by
    simp only [KeccakfPermAir.extraction.inter_5233, KeccakfPermAir.extraction.inter_5232, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5231 c row = (mc 1750 + mc 2205 - mc 2087*mc 2205 - 2*mc 1750*mc 2205 + 2*mc 1750*mc 2087*mc 2205) + 2 * KeccakfPermAir.extraction.inter_5229 c row := by
    simp only [KeccakfPermAir.extraction.inter_5231, KeccakfPermAir.extraction.inter_5230, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5229 c row = (mc 1751 + mc 2206 - mc 2088*mc 2206 - 2*mc 1751*mc 2206 + 2*mc 1751*mc 2088*mc 2206) := by
    simp only [KeccakfPermAir.extraction.inter_5229, KeccakfPermAir.extraction.inter_5228, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2959 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2959 c row) :
    ((mc 1752 + mc 2207 - mc 2089*mc 2207 - 2*mc 1752*mc 2207 + 2*mc 1752*mc 2089*mc 2207) + 2*(mc 1753 + mc 2208 - mc 2090*mc 2208 - 2*mc 1753*mc 2208 + 2*mc 1753*mc 2090*mc 2208) + 4*(mc 1754 + mc 2145 - mc 2091*mc 2145 - 2*mc 1754*mc 2145 + 2*mc 1754*mc 2091*mc 2145) + 8*(mc 1755 + mc 2146 - mc 2092*mc 2146 - 2*mc 1755*mc 2146 + 2*mc 1755*mc 2092*mc 2146) + 16*(mc 1756 + mc 2147 - mc 2093*mc 2147 - 2*mc 1756*mc 2147 + 2*mc 1756*mc 2093*mc 2147) + 32*(mc 1757 + mc 2148 - mc 2094*mc 2148 - 2*mc 1757*mc 2148 + 2*mc 1757*mc 2094*mc 2148) + 64*(mc 1758 + mc 2149 - mc 2095*mc 2149 - 2*mc 1758*mc 2149 + 2*mc 1758*mc 2095*mc 2149) + 128*(mc 1759 + mc 2150 - mc 2096*mc 2150 - 2*mc 1759*mc 2150 + 2*mc 1759*mc 2096*mc 2150) + 256*(mc 1760 + mc 2151 - mc 2097*mc 2151 - 2*mc 1760*mc 2151 + 2*mc 1760*mc 2097*mc 2151) + 512*(mc 1697 + mc 2152 - mc 2098*mc 2152 - 2*mc 1697*mc 2152 + 2*mc 1697*mc 2098*mc 2152) + 1024*(mc 1698 + mc 2153 - mc 2099*mc 2153 - 2*mc 1698*mc 2153 + 2*mc 1698*mc 2099*mc 2153) + 2048*(mc 1699 + mc 2154 - mc 2100*mc 2154 - 2*mc 1699*mc 2154 + 2*mc 1699*mc 2100*mc 2154) + 4096*(mc 1700 + mc 2155 - mc 2101*mc 2155 - 2*mc 1700*mc 2155 + 2*mc 1700*mc 2101*mc 2155) + 8192*(mc 1701 + mc 2156 - mc 2102*mc 2156 - 2*mc 1701*mc 2156 + 2*mc 1701*mc 2102*mc 2156) + 16384*(mc 1702 + mc 2157 - mc 2103*mc 2157 - 2*mc 1702*mc 2157 + 2*mc 1702*mc 2103*mc 2157) + 32768*(mc 1703 + mc 2158 - mc 2104*mc 2158 - 2*mc 1703*mc 2158 + 2*mc 1703*mc 2104*mc 2158)) - mc 2514 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2959, KeccakfPermAir.extraction.inter_5289, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5288 c row = (mc 1753 + mc 2208 - mc 2090*mc 2208 - 2*mc 1753*mc 2208 + 2*mc 1753*mc 2090*mc 2208) + 2 * KeccakfPermAir.extraction.inter_5286 c row := by
    simp only [KeccakfPermAir.extraction.inter_5288, KeccakfPermAir.extraction.inter_5287, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5286 c row = (mc 1754 + mc 2145 - mc 2091*mc 2145 - 2*mc 1754*mc 2145 + 2*mc 1754*mc 2091*mc 2145) + 2 * KeccakfPermAir.extraction.inter_5284 c row := by
    simp only [KeccakfPermAir.extraction.inter_5286, KeccakfPermAir.extraction.inter_5285, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5284 c row = (mc 1755 + mc 2146 - mc 2092*mc 2146 - 2*mc 1755*mc 2146 + 2*mc 1755*mc 2092*mc 2146) + 2 * KeccakfPermAir.extraction.inter_5282 c row := by
    simp only [KeccakfPermAir.extraction.inter_5284, KeccakfPermAir.extraction.inter_5283, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5282 c row = (mc 1756 + mc 2147 - mc 2093*mc 2147 - 2*mc 1756*mc 2147 + 2*mc 1756*mc 2093*mc 2147) + 2 * KeccakfPermAir.extraction.inter_5280 c row := by
    simp only [KeccakfPermAir.extraction.inter_5282, KeccakfPermAir.extraction.inter_5281, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5280 c row = (mc 1757 + mc 2148 - mc 2094*mc 2148 - 2*mc 1757*mc 2148 + 2*mc 1757*mc 2094*mc 2148) + 2 * KeccakfPermAir.extraction.inter_5278 c row := by
    simp only [KeccakfPermAir.extraction.inter_5280, KeccakfPermAir.extraction.inter_5279, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5278 c row = (mc 1758 + mc 2149 - mc 2095*mc 2149 - 2*mc 1758*mc 2149 + 2*mc 1758*mc 2095*mc 2149) + 2 * KeccakfPermAir.extraction.inter_5276 c row := by
    simp only [KeccakfPermAir.extraction.inter_5278, KeccakfPermAir.extraction.inter_5277, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5276 c row = (mc 1759 + mc 2150 - mc 2096*mc 2150 - 2*mc 1759*mc 2150 + 2*mc 1759*mc 2096*mc 2150) + 2 * KeccakfPermAir.extraction.inter_5274 c row := by
    simp only [KeccakfPermAir.extraction.inter_5276, KeccakfPermAir.extraction.inter_5275, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5274 c row = (mc 1760 + mc 2151 - mc 2097*mc 2151 - 2*mc 1760*mc 2151 + 2*mc 1760*mc 2097*mc 2151) + 2 * KeccakfPermAir.extraction.inter_5272 c row := by
    simp only [KeccakfPermAir.extraction.inter_5274, KeccakfPermAir.extraction.inter_5273, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5272 c row = (mc 1697 + mc 2152 - mc 2098*mc 2152 - 2*mc 1697*mc 2152 + 2*mc 1697*mc 2098*mc 2152) + 2 * KeccakfPermAir.extraction.inter_5270 c row := by
    simp only [KeccakfPermAir.extraction.inter_5272, KeccakfPermAir.extraction.inter_5271, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5270 c row = (mc 1698 + mc 2153 - mc 2099*mc 2153 - 2*mc 1698*mc 2153 + 2*mc 1698*mc 2099*mc 2153) + 2 * KeccakfPermAir.extraction.inter_5268 c row := by
    simp only [KeccakfPermAir.extraction.inter_5270, KeccakfPermAir.extraction.inter_5269, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5268 c row = (mc 1699 + mc 2154 - mc 2100*mc 2154 - 2*mc 1699*mc 2154 + 2*mc 1699*mc 2100*mc 2154) + 2 * KeccakfPermAir.extraction.inter_5266 c row := by
    simp only [KeccakfPermAir.extraction.inter_5268, KeccakfPermAir.extraction.inter_5267, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5266 c row = (mc 1700 + mc 2155 - mc 2101*mc 2155 - 2*mc 1700*mc 2155 + 2*mc 1700*mc 2101*mc 2155) + 2 * KeccakfPermAir.extraction.inter_5264 c row := by
    simp only [KeccakfPermAir.extraction.inter_5266, KeccakfPermAir.extraction.inter_5265, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5264 c row = (mc 1701 + mc 2156 - mc 2102*mc 2156 - 2*mc 1701*mc 2156 + 2*mc 1701*mc 2102*mc 2156) + 2 * KeccakfPermAir.extraction.inter_5262 c row := by
    simp only [KeccakfPermAir.extraction.inter_5264, KeccakfPermAir.extraction.inter_5263, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5262 c row = (mc 1702 + mc 2157 - mc 2103*mc 2157 - 2*mc 1702*mc 2157 + 2*mc 1702*mc 2103*mc 2157) + 2 * KeccakfPermAir.extraction.inter_5260 c row := by
    simp only [KeccakfPermAir.extraction.inter_5262, KeccakfPermAir.extraction.inter_5261, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5260 c row = (mc 1703 + mc 2158 - mc 2104*mc 2158 - 2*mc 1703*mc 2158 + 2*mc 1703*mc 2104*mc 2158) := by
    simp only [KeccakfPermAir.extraction.inter_5260, KeccakfPermAir.extraction.inter_5259, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2960 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2960 c row) :
    ((mc 1704 + mc 2159 - mc 2105*mc 2159 - 2*mc 1704*mc 2159 + 2*mc 1704*mc 2105*mc 2159) + 2*(mc 1705 + mc 2160 - mc 2106*mc 2160 - 2*mc 1705*mc 2160 + 2*mc 1705*mc 2106*mc 2160) + 4*(mc 1706 + mc 2161 - mc 2107*mc 2161 - 2*mc 1706*mc 2161 + 2*mc 1706*mc 2107*mc 2161) + 8*(mc 1707 + mc 2162 - mc 2108*mc 2162 - 2*mc 1707*mc 2162 + 2*mc 1707*mc 2108*mc 2162) + 16*(mc 1708 + mc 2163 - mc 2109*mc 2163 - 2*mc 1708*mc 2163 + 2*mc 1708*mc 2109*mc 2163) + 32*(mc 1709 + mc 2164 - mc 2110*mc 2164 - 2*mc 1709*mc 2164 + 2*mc 1709*mc 2110*mc 2164) + 64*(mc 1710 + mc 2165 - mc 2111*mc 2165 - 2*mc 1710*mc 2165 + 2*mc 1710*mc 2111*mc 2165) + 128*(mc 1711 + mc 2166 - mc 2112*mc 2166 - 2*mc 1711*mc 2166 + 2*mc 1711*mc 2112*mc 2166) + 256*(mc 1712 + mc 2167 - mc 2113*mc 2167 - 2*mc 1712*mc 2167 + 2*mc 1712*mc 2113*mc 2167) + 512*(mc 1713 + mc 2168 - mc 2114*mc 2168 - 2*mc 1713*mc 2168 + 2*mc 1713*mc 2114*mc 2168) + 1024*(mc 1714 + mc 2169 - mc 2115*mc 2169 - 2*mc 1714*mc 2169 + 2*mc 1714*mc 2115*mc 2169) + 2048*(mc 1715 + mc 2170 - mc 2116*mc 2170 - 2*mc 1715*mc 2170 + 2*mc 1715*mc 2116*mc 2170) + 4096*(mc 1716 + mc 2171 - mc 2117*mc 2171 - 2*mc 1716*mc 2171 + 2*mc 1716*mc 2117*mc 2171) + 8192*(mc 1717 + mc 2172 - mc 2118*mc 2172 - 2*mc 1717*mc 2172 + 2*mc 1717*mc 2118*mc 2172) + 16384*(mc 1718 + mc 2173 - mc 2119*mc 2173 - 2*mc 1718*mc 2173 + 2*mc 1718*mc 2119*mc 2173) + 32768*(mc 1719 + mc 2174 - mc 2120*mc 2174 - 2*mc 1719*mc 2174 + 2*mc 1719*mc 2120*mc 2174)) - mc 2515 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2960, KeccakfPermAir.extraction.inter_5320, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5319 c row = (mc 1705 + mc 2160 - mc 2106*mc 2160 - 2*mc 1705*mc 2160 + 2*mc 1705*mc 2106*mc 2160) + 2 * KeccakfPermAir.extraction.inter_5317 c row := by
    simp only [KeccakfPermAir.extraction.inter_5319, KeccakfPermAir.extraction.inter_5318, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5317 c row = (mc 1706 + mc 2161 - mc 2107*mc 2161 - 2*mc 1706*mc 2161 + 2*mc 1706*mc 2107*mc 2161) + 2 * KeccakfPermAir.extraction.inter_5315 c row := by
    simp only [KeccakfPermAir.extraction.inter_5317, KeccakfPermAir.extraction.inter_5316, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5315 c row = (mc 1707 + mc 2162 - mc 2108*mc 2162 - 2*mc 1707*mc 2162 + 2*mc 1707*mc 2108*mc 2162) + 2 * KeccakfPermAir.extraction.inter_5313 c row := by
    simp only [KeccakfPermAir.extraction.inter_5315, KeccakfPermAir.extraction.inter_5314, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5313 c row = (mc 1708 + mc 2163 - mc 2109*mc 2163 - 2*mc 1708*mc 2163 + 2*mc 1708*mc 2109*mc 2163) + 2 * KeccakfPermAir.extraction.inter_5311 c row := by
    simp only [KeccakfPermAir.extraction.inter_5313, KeccakfPermAir.extraction.inter_5312, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5311 c row = (mc 1709 + mc 2164 - mc 2110*mc 2164 - 2*mc 1709*mc 2164 + 2*mc 1709*mc 2110*mc 2164) + 2 * KeccakfPermAir.extraction.inter_5309 c row := by
    simp only [KeccakfPermAir.extraction.inter_5311, KeccakfPermAir.extraction.inter_5310, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5309 c row = (mc 1710 + mc 2165 - mc 2111*mc 2165 - 2*mc 1710*mc 2165 + 2*mc 1710*mc 2111*mc 2165) + 2 * KeccakfPermAir.extraction.inter_5307 c row := by
    simp only [KeccakfPermAir.extraction.inter_5309, KeccakfPermAir.extraction.inter_5308, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5307 c row = (mc 1711 + mc 2166 - mc 2112*mc 2166 - 2*mc 1711*mc 2166 + 2*mc 1711*mc 2112*mc 2166) + 2 * KeccakfPermAir.extraction.inter_5305 c row := by
    simp only [KeccakfPermAir.extraction.inter_5307, KeccakfPermAir.extraction.inter_5306, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5305 c row = (mc 1712 + mc 2167 - mc 2113*mc 2167 - 2*mc 1712*mc 2167 + 2*mc 1712*mc 2113*mc 2167) + 2 * KeccakfPermAir.extraction.inter_5303 c row := by
    simp only [KeccakfPermAir.extraction.inter_5305, KeccakfPermAir.extraction.inter_5304, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5303 c row = (mc 1713 + mc 2168 - mc 2114*mc 2168 - 2*mc 1713*mc 2168 + 2*mc 1713*mc 2114*mc 2168) + 2 * KeccakfPermAir.extraction.inter_5301 c row := by
    simp only [KeccakfPermAir.extraction.inter_5303, KeccakfPermAir.extraction.inter_5302, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5301 c row = (mc 1714 + mc 2169 - mc 2115*mc 2169 - 2*mc 1714*mc 2169 + 2*mc 1714*mc 2115*mc 2169) + 2 * KeccakfPermAir.extraction.inter_5299 c row := by
    simp only [KeccakfPermAir.extraction.inter_5301, KeccakfPermAir.extraction.inter_5300, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5299 c row = (mc 1715 + mc 2170 - mc 2116*mc 2170 - 2*mc 1715*mc 2170 + 2*mc 1715*mc 2116*mc 2170) + 2 * KeccakfPermAir.extraction.inter_5297 c row := by
    simp only [KeccakfPermAir.extraction.inter_5299, KeccakfPermAir.extraction.inter_5298, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5297 c row = (mc 1716 + mc 2171 - mc 2117*mc 2171 - 2*mc 1716*mc 2171 + 2*mc 1716*mc 2117*mc 2171) + 2 * KeccakfPermAir.extraction.inter_5295 c row := by
    simp only [KeccakfPermAir.extraction.inter_5297, KeccakfPermAir.extraction.inter_5296, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5295 c row = (mc 1717 + mc 2172 - mc 2118*mc 2172 - 2*mc 1717*mc 2172 + 2*mc 1717*mc 2118*mc 2172) + 2 * KeccakfPermAir.extraction.inter_5293 c row := by
    simp only [KeccakfPermAir.extraction.inter_5295, KeccakfPermAir.extraction.inter_5294, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5293 c row = (mc 1718 + mc 2173 - mc 2119*mc 2173 - 2*mc 1718*mc 2173 + 2*mc 1718*mc 2119*mc 2173) + 2 * KeccakfPermAir.extraction.inter_5291 c row := by
    simp only [KeccakfPermAir.extraction.inter_5293, KeccakfPermAir.extraction.inter_5292, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5291 c row = (mc 1719 + mc 2174 - mc 2120*mc 2174 - 2*mc 1719*mc 2174 + 2*mc 1719*mc 2120*mc 2174) := by
    simp only [KeccakfPermAir.extraction.inter_5291, KeccakfPermAir.extraction.inter_5290, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2961 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2961 c row) :
    ((mc 1720 + mc 2175 - mc 2121*mc 2175 - 2*mc 1720*mc 2175 + 2*mc 1720*mc 2121*mc 2175) + 2*(mc 1721 + mc 2176 - mc 2122*mc 2176 - 2*mc 1721*mc 2176 + 2*mc 1721*mc 2122*mc 2176) + 4*(mc 1722 + mc 2177 - mc 2123*mc 2177 - 2*mc 1722*mc 2177 + 2*mc 1722*mc 2123*mc 2177) + 8*(mc 1723 + mc 2178 - mc 2124*mc 2178 - 2*mc 1723*mc 2178 + 2*mc 1723*mc 2124*mc 2178) + 16*(mc 1724 + mc 2179 - mc 2125*mc 2179 - 2*mc 1724*mc 2179 + 2*mc 1724*mc 2125*mc 2179) + 32*(mc 1725 + mc 2180 - mc 2126*mc 2180 - 2*mc 1725*mc 2180 + 2*mc 1725*mc 2126*mc 2180) + 64*(mc 1726 + mc 2181 - mc 2127*mc 2181 - 2*mc 1726*mc 2181 + 2*mc 1726*mc 2127*mc 2181) + 128*(mc 1727 + mc 2182 - mc 2128*mc 2182 - 2*mc 1727*mc 2182 + 2*mc 1727*mc 2128*mc 2182) + 256*(mc 1728 + mc 2183 - mc 2129*mc 2183 - 2*mc 1728*mc 2183 + 2*mc 1728*mc 2129*mc 2183) + 512*(mc 1729 + mc 2184 - mc 2130*mc 2184 - 2*mc 1729*mc 2184 + 2*mc 1729*mc 2130*mc 2184) + 1024*(mc 1730 + mc 2185 - mc 2131*mc 2185 - 2*mc 1730*mc 2185 + 2*mc 1730*mc 2131*mc 2185) + 2048*(mc 1731 + mc 2186 - mc 2132*mc 2186 - 2*mc 1731*mc 2186 + 2*mc 1731*mc 2132*mc 2186) + 4096*(mc 1732 + mc 2187 - mc 2133*mc 2187 - 2*mc 1732*mc 2187 + 2*mc 1732*mc 2133*mc 2187) + 8192*(mc 1733 + mc 2188 - mc 2134*mc 2188 - 2*mc 1733*mc 2188 + 2*mc 1733*mc 2134*mc 2188) + 16384*(mc 1734 + mc 2189 - mc 2135*mc 2189 - 2*mc 1734*mc 2189 + 2*mc 1734*mc 2135*mc 2189) + 32768*(mc 1735 + mc 2190 - mc 2136*mc 2190 - 2*mc 1735*mc 2190 + 2*mc 1735*mc 2136*mc 2190)) - mc 2516 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2961, KeccakfPermAir.extraction.inter_5351, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5350 c row = (mc 1721 + mc 2176 - mc 2122*mc 2176 - 2*mc 1721*mc 2176 + 2*mc 1721*mc 2122*mc 2176) + 2 * KeccakfPermAir.extraction.inter_5348 c row := by
    simp only [KeccakfPermAir.extraction.inter_5350, KeccakfPermAir.extraction.inter_5349, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5348 c row = (mc 1722 + mc 2177 - mc 2123*mc 2177 - 2*mc 1722*mc 2177 + 2*mc 1722*mc 2123*mc 2177) + 2 * KeccakfPermAir.extraction.inter_5346 c row := by
    simp only [KeccakfPermAir.extraction.inter_5348, KeccakfPermAir.extraction.inter_5347, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5346 c row = (mc 1723 + mc 2178 - mc 2124*mc 2178 - 2*mc 1723*mc 2178 + 2*mc 1723*mc 2124*mc 2178) + 2 * KeccakfPermAir.extraction.inter_5344 c row := by
    simp only [KeccakfPermAir.extraction.inter_5346, KeccakfPermAir.extraction.inter_5345, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5344 c row = (mc 1724 + mc 2179 - mc 2125*mc 2179 - 2*mc 1724*mc 2179 + 2*mc 1724*mc 2125*mc 2179) + 2 * KeccakfPermAir.extraction.inter_5342 c row := by
    simp only [KeccakfPermAir.extraction.inter_5344, KeccakfPermAir.extraction.inter_5343, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5342 c row = (mc 1725 + mc 2180 - mc 2126*mc 2180 - 2*mc 1725*mc 2180 + 2*mc 1725*mc 2126*mc 2180) + 2 * KeccakfPermAir.extraction.inter_5340 c row := by
    simp only [KeccakfPermAir.extraction.inter_5342, KeccakfPermAir.extraction.inter_5341, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5340 c row = (mc 1726 + mc 2181 - mc 2127*mc 2181 - 2*mc 1726*mc 2181 + 2*mc 1726*mc 2127*mc 2181) + 2 * KeccakfPermAir.extraction.inter_5338 c row := by
    simp only [KeccakfPermAir.extraction.inter_5340, KeccakfPermAir.extraction.inter_5339, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5338 c row = (mc 1727 + mc 2182 - mc 2128*mc 2182 - 2*mc 1727*mc 2182 + 2*mc 1727*mc 2128*mc 2182) + 2 * KeccakfPermAir.extraction.inter_5336 c row := by
    simp only [KeccakfPermAir.extraction.inter_5338, KeccakfPermAir.extraction.inter_5337, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5336 c row = (mc 1728 + mc 2183 - mc 2129*mc 2183 - 2*mc 1728*mc 2183 + 2*mc 1728*mc 2129*mc 2183) + 2 * KeccakfPermAir.extraction.inter_5334 c row := by
    simp only [KeccakfPermAir.extraction.inter_5336, KeccakfPermAir.extraction.inter_5335, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5334 c row = (mc 1729 + mc 2184 - mc 2130*mc 2184 - 2*mc 1729*mc 2184 + 2*mc 1729*mc 2130*mc 2184) + 2 * KeccakfPermAir.extraction.inter_5332 c row := by
    simp only [KeccakfPermAir.extraction.inter_5334, KeccakfPermAir.extraction.inter_5333, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5332 c row = (mc 1730 + mc 2185 - mc 2131*mc 2185 - 2*mc 1730*mc 2185 + 2*mc 1730*mc 2131*mc 2185) + 2 * KeccakfPermAir.extraction.inter_5330 c row := by
    simp only [KeccakfPermAir.extraction.inter_5332, KeccakfPermAir.extraction.inter_5331, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5330 c row = (mc 1731 + mc 2186 - mc 2132*mc 2186 - 2*mc 1731*mc 2186 + 2*mc 1731*mc 2132*mc 2186) + 2 * KeccakfPermAir.extraction.inter_5328 c row := by
    simp only [KeccakfPermAir.extraction.inter_5330, KeccakfPermAir.extraction.inter_5329, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5328 c row = (mc 1732 + mc 2187 - mc 2133*mc 2187 - 2*mc 1732*mc 2187 + 2*mc 1732*mc 2133*mc 2187) + 2 * KeccakfPermAir.extraction.inter_5326 c row := by
    simp only [KeccakfPermAir.extraction.inter_5328, KeccakfPermAir.extraction.inter_5327, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5326 c row = (mc 1733 + mc 2188 - mc 2134*mc 2188 - 2*mc 1733*mc 2188 + 2*mc 1733*mc 2134*mc 2188) + 2 * KeccakfPermAir.extraction.inter_5324 c row := by
    simp only [KeccakfPermAir.extraction.inter_5326, KeccakfPermAir.extraction.inter_5325, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5324 c row = (mc 1734 + mc 2189 - mc 2135*mc 2189 - 2*mc 1734*mc 2189 + 2*mc 1734*mc 2135*mc 2189) + 2 * KeccakfPermAir.extraction.inter_5322 c row := by
    simp only [KeccakfPermAir.extraction.inter_5324, KeccakfPermAir.extraction.inter_5323, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5322 c row = (mc 1735 + mc 2190 - mc 2136*mc 2190 - 2*mc 1735*mc 2190 + 2*mc 1735*mc 2136*mc 2190) := by
    simp only [KeccakfPermAir.extraction.inter_5322, KeccakfPermAir.extraction.inter_5321, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2962 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2962 c row) :
    ((mc 2137 + mc 992 - mc 2191*mc 992 - 2*mc 2137*mc 992 + 2*mc 2137*mc 2191*mc 992) + 2*(mc 2138 + mc 929 - mc 2192*mc 929 - 2*mc 2138*mc 929 + 2*mc 2138*mc 2192*mc 929) + 4*(mc 2139 + mc 930 - mc 2193*mc 930 - 2*mc 2139*mc 930 + 2*mc 2139*mc 2193*mc 930) + 8*(mc 2140 + mc 931 - mc 2194*mc 931 - 2*mc 2140*mc 931 + 2*mc 2140*mc 2194*mc 931) + 16*(mc 2141 + mc 932 - mc 2195*mc 932 - 2*mc 2141*mc 932 + 2*mc 2141*mc 2195*mc 932) + 32*(mc 2142 + mc 933 - mc 2196*mc 933 - 2*mc 2142*mc 933 + 2*mc 2142*mc 2196*mc 933) + 64*(mc 2143 + mc 934 - mc 2197*mc 934 - 2*mc 2143*mc 934 + 2*mc 2143*mc 2197*mc 934) + 128*(mc 2144 + mc 935 - mc 2198*mc 935 - 2*mc 2144*mc 935 + 2*mc 2144*mc 2198*mc 935) + 256*(mc 2081 + mc 936 - mc 2199*mc 936 - 2*mc 2081*mc 936 + 2*mc 2081*mc 2199*mc 936) + 512*(mc 2082 + mc 937 - mc 2200*mc 937 - 2*mc 2082*mc 937 + 2*mc 2082*mc 2200*mc 937) + 1024*(mc 2083 + mc 938 - mc 2201*mc 938 - 2*mc 2083*mc 938 + 2*mc 2083*mc 2201*mc 938) + 2048*(mc 2084 + mc 939 - mc 2202*mc 939 - 2*mc 2084*mc 939 + 2*mc 2084*mc 2202*mc 939) + 4096*(mc 2085 + mc 940 - mc 2203*mc 940 - 2*mc 2085*mc 940 + 2*mc 2085*mc 2203*mc 940) + 8192*(mc 2086 + mc 941 - mc 2204*mc 941 - 2*mc 2086*mc 941 + 2*mc 2086*mc 2204*mc 941) + 16384*(mc 2087 + mc 942 - mc 2205*mc 942 - 2*mc 2087*mc 942 + 2*mc 2087*mc 2205*mc 942) + 32768*(mc 2088 + mc 943 - mc 2206*mc 943 - 2*mc 2088*mc 943 + 2*mc 2088*mc 2206*mc 943)) - mc 2517 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2962, KeccakfPermAir.extraction.inter_5382, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5381 c row = (mc 2138 + mc 929 - mc 2192*mc 929 - 2*mc 2138*mc 929 + 2*mc 2138*mc 2192*mc 929) + 2 * KeccakfPermAir.extraction.inter_5379 c row := by
    simp only [KeccakfPermAir.extraction.inter_5381, KeccakfPermAir.extraction.inter_5380, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5379 c row = (mc 2139 + mc 930 - mc 2193*mc 930 - 2*mc 2139*mc 930 + 2*mc 2139*mc 2193*mc 930) + 2 * KeccakfPermAir.extraction.inter_5377 c row := by
    simp only [KeccakfPermAir.extraction.inter_5379, KeccakfPermAir.extraction.inter_5378, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5377 c row = (mc 2140 + mc 931 - mc 2194*mc 931 - 2*mc 2140*mc 931 + 2*mc 2140*mc 2194*mc 931) + 2 * KeccakfPermAir.extraction.inter_5375 c row := by
    simp only [KeccakfPermAir.extraction.inter_5377, KeccakfPermAir.extraction.inter_5376, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5375 c row = (mc 2141 + mc 932 - mc 2195*mc 932 - 2*mc 2141*mc 932 + 2*mc 2141*mc 2195*mc 932) + 2 * KeccakfPermAir.extraction.inter_5373 c row := by
    simp only [KeccakfPermAir.extraction.inter_5375, KeccakfPermAir.extraction.inter_5374, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5373 c row = (mc 2142 + mc 933 - mc 2196*mc 933 - 2*mc 2142*mc 933 + 2*mc 2142*mc 2196*mc 933) + 2 * KeccakfPermAir.extraction.inter_5371 c row := by
    simp only [KeccakfPermAir.extraction.inter_5373, KeccakfPermAir.extraction.inter_5372, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5371 c row = (mc 2143 + mc 934 - mc 2197*mc 934 - 2*mc 2143*mc 934 + 2*mc 2143*mc 2197*mc 934) + 2 * KeccakfPermAir.extraction.inter_5369 c row := by
    simp only [KeccakfPermAir.extraction.inter_5371, KeccakfPermAir.extraction.inter_5370, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5369 c row = (mc 2144 + mc 935 - mc 2198*mc 935 - 2*mc 2144*mc 935 + 2*mc 2144*mc 2198*mc 935) + 2 * KeccakfPermAir.extraction.inter_5367 c row := by
    simp only [KeccakfPermAir.extraction.inter_5369, KeccakfPermAir.extraction.inter_5368, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5367 c row = (mc 2081 + mc 936 - mc 2199*mc 936 - 2*mc 2081*mc 936 + 2*mc 2081*mc 2199*mc 936) + 2 * KeccakfPermAir.extraction.inter_5365 c row := by
    simp only [KeccakfPermAir.extraction.inter_5367, KeccakfPermAir.extraction.inter_5366, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5365 c row = (mc 2082 + mc 937 - mc 2200*mc 937 - 2*mc 2082*mc 937 + 2*mc 2082*mc 2200*mc 937) + 2 * KeccakfPermAir.extraction.inter_5363 c row := by
    simp only [KeccakfPermAir.extraction.inter_5365, KeccakfPermAir.extraction.inter_5364, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5363 c row = (mc 2083 + mc 938 - mc 2201*mc 938 - 2*mc 2083*mc 938 + 2*mc 2083*mc 2201*mc 938) + 2 * KeccakfPermAir.extraction.inter_5361 c row := by
    simp only [KeccakfPermAir.extraction.inter_5363, KeccakfPermAir.extraction.inter_5362, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5361 c row = (mc 2084 + mc 939 - mc 2202*mc 939 - 2*mc 2084*mc 939 + 2*mc 2084*mc 2202*mc 939) + 2 * KeccakfPermAir.extraction.inter_5359 c row := by
    simp only [KeccakfPermAir.extraction.inter_5361, KeccakfPermAir.extraction.inter_5360, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5359 c row = (mc 2085 + mc 940 - mc 2203*mc 940 - 2*mc 2085*mc 940 + 2*mc 2085*mc 2203*mc 940) + 2 * KeccakfPermAir.extraction.inter_5357 c row := by
    simp only [KeccakfPermAir.extraction.inter_5359, KeccakfPermAir.extraction.inter_5358, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5357 c row = (mc 2086 + mc 941 - mc 2204*mc 941 - 2*mc 2086*mc 941 + 2*mc 2086*mc 2204*mc 941) + 2 * KeccakfPermAir.extraction.inter_5355 c row := by
    simp only [KeccakfPermAir.extraction.inter_5357, KeccakfPermAir.extraction.inter_5356, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5355 c row = (mc 2087 + mc 942 - mc 2205*mc 942 - 2*mc 2087*mc 942 + 2*mc 2087*mc 2205*mc 942) + 2 * KeccakfPermAir.extraction.inter_5353 c row := by
    simp only [KeccakfPermAir.extraction.inter_5355, KeccakfPermAir.extraction.inter_5354, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5353 c row = (mc 2088 + mc 943 - mc 2206*mc 943 - 2*mc 2088*mc 943 + 2*mc 2088*mc 2206*mc 943) := by
    simp only [KeccakfPermAir.extraction.inter_5353, KeccakfPermAir.extraction.inter_5352, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2963 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2963 c row) :
    ((mc 2089 + mc 944 - mc 2207*mc 944 - 2*mc 2089*mc 944 + 2*mc 2089*mc 2207*mc 944) + 2*(mc 2090 + mc 945 - mc 2208*mc 945 - 2*mc 2090*mc 945 + 2*mc 2090*mc 2208*mc 945) + 4*(mc 2091 + mc 946 - mc 2145*mc 946 - 2*mc 2091*mc 946 + 2*mc 2091*mc 2145*mc 946) + 8*(mc 2092 + mc 947 - mc 2146*mc 947 - 2*mc 2092*mc 947 + 2*mc 2092*mc 2146*mc 947) + 16*(mc 2093 + mc 948 - mc 2147*mc 948 - 2*mc 2093*mc 948 + 2*mc 2093*mc 2147*mc 948) + 32*(mc 2094 + mc 949 - mc 2148*mc 949 - 2*mc 2094*mc 949 + 2*mc 2094*mc 2148*mc 949) + 64*(mc 2095 + mc 950 - mc 2149*mc 950 - 2*mc 2095*mc 950 + 2*mc 2095*mc 2149*mc 950) + 128*(mc 2096 + mc 951 - mc 2150*mc 951 - 2*mc 2096*mc 951 + 2*mc 2096*mc 2150*mc 951) + 256*(mc 2097 + mc 952 - mc 2151*mc 952 - 2*mc 2097*mc 952 + 2*mc 2097*mc 2151*mc 952) + 512*(mc 2098 + mc 953 - mc 2152*mc 953 - 2*mc 2098*mc 953 + 2*mc 2098*mc 2152*mc 953) + 1024*(mc 2099 + mc 954 - mc 2153*mc 954 - 2*mc 2099*mc 954 + 2*mc 2099*mc 2153*mc 954) + 2048*(mc 2100 + mc 955 - mc 2154*mc 955 - 2*mc 2100*mc 955 + 2*mc 2100*mc 2154*mc 955) + 4096*(mc 2101 + mc 956 - mc 2155*mc 956 - 2*mc 2101*mc 956 + 2*mc 2101*mc 2155*mc 956) + 8192*(mc 2102 + mc 957 - mc 2156*mc 957 - 2*mc 2102*mc 957 + 2*mc 2102*mc 2156*mc 957) + 16384*(mc 2103 + mc 958 - mc 2157*mc 958 - 2*mc 2103*mc 958 + 2*mc 2103*mc 2157*mc 958) + 32768*(mc 2104 + mc 959 - mc 2158*mc 959 - 2*mc 2104*mc 959 + 2*mc 2104*mc 2158*mc 959)) - mc 2518 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2963, KeccakfPermAir.extraction.inter_5413, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5412 c row = (mc 2090 + mc 945 - mc 2208*mc 945 - 2*mc 2090*mc 945 + 2*mc 2090*mc 2208*mc 945) + 2 * KeccakfPermAir.extraction.inter_5410 c row := by
    simp only [KeccakfPermAir.extraction.inter_5412, KeccakfPermAir.extraction.inter_5411, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5410 c row = (mc 2091 + mc 946 - mc 2145*mc 946 - 2*mc 2091*mc 946 + 2*mc 2091*mc 2145*mc 946) + 2 * KeccakfPermAir.extraction.inter_5408 c row := by
    simp only [KeccakfPermAir.extraction.inter_5410, KeccakfPermAir.extraction.inter_5409, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5408 c row = (mc 2092 + mc 947 - mc 2146*mc 947 - 2*mc 2092*mc 947 + 2*mc 2092*mc 2146*mc 947) + 2 * KeccakfPermAir.extraction.inter_5406 c row := by
    simp only [KeccakfPermAir.extraction.inter_5408, KeccakfPermAir.extraction.inter_5407, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5406 c row = (mc 2093 + mc 948 - mc 2147*mc 948 - 2*mc 2093*mc 948 + 2*mc 2093*mc 2147*mc 948) + 2 * KeccakfPermAir.extraction.inter_5404 c row := by
    simp only [KeccakfPermAir.extraction.inter_5406, KeccakfPermAir.extraction.inter_5405, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5404 c row = (mc 2094 + mc 949 - mc 2148*mc 949 - 2*mc 2094*mc 949 + 2*mc 2094*mc 2148*mc 949) + 2 * KeccakfPermAir.extraction.inter_5402 c row := by
    simp only [KeccakfPermAir.extraction.inter_5404, KeccakfPermAir.extraction.inter_5403, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5402 c row = (mc 2095 + mc 950 - mc 2149*mc 950 - 2*mc 2095*mc 950 + 2*mc 2095*mc 2149*mc 950) + 2 * KeccakfPermAir.extraction.inter_5400 c row := by
    simp only [KeccakfPermAir.extraction.inter_5402, KeccakfPermAir.extraction.inter_5401, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5400 c row = (mc 2096 + mc 951 - mc 2150*mc 951 - 2*mc 2096*mc 951 + 2*mc 2096*mc 2150*mc 951) + 2 * KeccakfPermAir.extraction.inter_5398 c row := by
    simp only [KeccakfPermAir.extraction.inter_5400, KeccakfPermAir.extraction.inter_5399, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5398 c row = (mc 2097 + mc 952 - mc 2151*mc 952 - 2*mc 2097*mc 952 + 2*mc 2097*mc 2151*mc 952) + 2 * KeccakfPermAir.extraction.inter_5396 c row := by
    simp only [KeccakfPermAir.extraction.inter_5398, KeccakfPermAir.extraction.inter_5397, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5396 c row = (mc 2098 + mc 953 - mc 2152*mc 953 - 2*mc 2098*mc 953 + 2*mc 2098*mc 2152*mc 953) + 2 * KeccakfPermAir.extraction.inter_5394 c row := by
    simp only [KeccakfPermAir.extraction.inter_5396, KeccakfPermAir.extraction.inter_5395, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5394 c row = (mc 2099 + mc 954 - mc 2153*mc 954 - 2*mc 2099*mc 954 + 2*mc 2099*mc 2153*mc 954) + 2 * KeccakfPermAir.extraction.inter_5392 c row := by
    simp only [KeccakfPermAir.extraction.inter_5394, KeccakfPermAir.extraction.inter_5393, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5392 c row = (mc 2100 + mc 955 - mc 2154*mc 955 - 2*mc 2100*mc 955 + 2*mc 2100*mc 2154*mc 955) + 2 * KeccakfPermAir.extraction.inter_5390 c row := by
    simp only [KeccakfPermAir.extraction.inter_5392, KeccakfPermAir.extraction.inter_5391, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5390 c row = (mc 2101 + mc 956 - mc 2155*mc 956 - 2*mc 2101*mc 956 + 2*mc 2101*mc 2155*mc 956) + 2 * KeccakfPermAir.extraction.inter_5388 c row := by
    simp only [KeccakfPermAir.extraction.inter_5390, KeccakfPermAir.extraction.inter_5389, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5388 c row = (mc 2102 + mc 957 - mc 2156*mc 957 - 2*mc 2102*mc 957 + 2*mc 2102*mc 2156*mc 957) + 2 * KeccakfPermAir.extraction.inter_5386 c row := by
    simp only [KeccakfPermAir.extraction.inter_5388, KeccakfPermAir.extraction.inter_5387, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5386 c row = (mc 2103 + mc 958 - mc 2157*mc 958 - 2*mc 2103*mc 958 + 2*mc 2103*mc 2157*mc 958) + 2 * KeccakfPermAir.extraction.inter_5384 c row := by
    simp only [KeccakfPermAir.extraction.inter_5386, KeccakfPermAir.extraction.inter_5385, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5384 c row = (mc 2104 + mc 959 - mc 2158*mc 959 - 2*mc 2104*mc 959 + 2*mc 2104*mc 2158*mc 959) := by
    simp only [KeccakfPermAir.extraction.inter_5384, KeccakfPermAir.extraction.inter_5383, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2964 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2964 c row) :
    ((mc 2105 + mc 960 - mc 2159*mc 960 - 2*mc 2105*mc 960 + 2*mc 2105*mc 2159*mc 960) + 2*(mc 2106 + mc 961 - mc 2160*mc 961 - 2*mc 2106*mc 961 + 2*mc 2106*mc 2160*mc 961) + 4*(mc 2107 + mc 962 - mc 2161*mc 962 - 2*mc 2107*mc 962 + 2*mc 2107*mc 2161*mc 962) + 8*(mc 2108 + mc 963 - mc 2162*mc 963 - 2*mc 2108*mc 963 + 2*mc 2108*mc 2162*mc 963) + 16*(mc 2109 + mc 964 - mc 2163*mc 964 - 2*mc 2109*mc 964 + 2*mc 2109*mc 2163*mc 964) + 32*(mc 2110 + mc 965 - mc 2164*mc 965 - 2*mc 2110*mc 965 + 2*mc 2110*mc 2164*mc 965) + 64*(mc 2111 + mc 966 - mc 2165*mc 966 - 2*mc 2111*mc 966 + 2*mc 2111*mc 2165*mc 966) + 128*(mc 2112 + mc 967 - mc 2166*mc 967 - 2*mc 2112*mc 967 + 2*mc 2112*mc 2166*mc 967) + 256*(mc 2113 + mc 968 - mc 2167*mc 968 - 2*mc 2113*mc 968 + 2*mc 2113*mc 2167*mc 968) + 512*(mc 2114 + mc 969 - mc 2168*mc 969 - 2*mc 2114*mc 969 + 2*mc 2114*mc 2168*mc 969) + 1024*(mc 2115 + mc 970 - mc 2169*mc 970 - 2*mc 2115*mc 970 + 2*mc 2115*mc 2169*mc 970) + 2048*(mc 2116 + mc 971 - mc 2170*mc 971 - 2*mc 2116*mc 971 + 2*mc 2116*mc 2170*mc 971) + 4096*(mc 2117 + mc 972 - mc 2171*mc 972 - 2*mc 2117*mc 972 + 2*mc 2117*mc 2171*mc 972) + 8192*(mc 2118 + mc 973 - mc 2172*mc 973 - 2*mc 2118*mc 973 + 2*mc 2118*mc 2172*mc 973) + 16384*(mc 2119 + mc 974 - mc 2173*mc 974 - 2*mc 2119*mc 974 + 2*mc 2119*mc 2173*mc 974) + 32768*(mc 2120 + mc 975 - mc 2174*mc 975 - 2*mc 2120*mc 975 + 2*mc 2120*mc 2174*mc 975)) - mc 2519 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2964, KeccakfPermAir.extraction.inter_5444, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5443 c row = (mc 2106 + mc 961 - mc 2160*mc 961 - 2*mc 2106*mc 961 + 2*mc 2106*mc 2160*mc 961) + 2 * KeccakfPermAir.extraction.inter_5441 c row := by
    simp only [KeccakfPermAir.extraction.inter_5443, KeccakfPermAir.extraction.inter_5442, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5441 c row = (mc 2107 + mc 962 - mc 2161*mc 962 - 2*mc 2107*mc 962 + 2*mc 2107*mc 2161*mc 962) + 2 * KeccakfPermAir.extraction.inter_5439 c row := by
    simp only [KeccakfPermAir.extraction.inter_5441, KeccakfPermAir.extraction.inter_5440, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5439 c row = (mc 2108 + mc 963 - mc 2162*mc 963 - 2*mc 2108*mc 963 + 2*mc 2108*mc 2162*mc 963) + 2 * KeccakfPermAir.extraction.inter_5437 c row := by
    simp only [KeccakfPermAir.extraction.inter_5439, KeccakfPermAir.extraction.inter_5438, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5437 c row = (mc 2109 + mc 964 - mc 2163*mc 964 - 2*mc 2109*mc 964 + 2*mc 2109*mc 2163*mc 964) + 2 * KeccakfPermAir.extraction.inter_5435 c row := by
    simp only [KeccakfPermAir.extraction.inter_5437, KeccakfPermAir.extraction.inter_5436, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5435 c row = (mc 2110 + mc 965 - mc 2164*mc 965 - 2*mc 2110*mc 965 + 2*mc 2110*mc 2164*mc 965) + 2 * KeccakfPermAir.extraction.inter_5433 c row := by
    simp only [KeccakfPermAir.extraction.inter_5435, KeccakfPermAir.extraction.inter_5434, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5433 c row = (mc 2111 + mc 966 - mc 2165*mc 966 - 2*mc 2111*mc 966 + 2*mc 2111*mc 2165*mc 966) + 2 * KeccakfPermAir.extraction.inter_5431 c row := by
    simp only [KeccakfPermAir.extraction.inter_5433, KeccakfPermAir.extraction.inter_5432, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5431 c row = (mc 2112 + mc 967 - mc 2166*mc 967 - 2*mc 2112*mc 967 + 2*mc 2112*mc 2166*mc 967) + 2 * KeccakfPermAir.extraction.inter_5429 c row := by
    simp only [KeccakfPermAir.extraction.inter_5431, KeccakfPermAir.extraction.inter_5430, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5429 c row = (mc 2113 + mc 968 - mc 2167*mc 968 - 2*mc 2113*mc 968 + 2*mc 2113*mc 2167*mc 968) + 2 * KeccakfPermAir.extraction.inter_5427 c row := by
    simp only [KeccakfPermAir.extraction.inter_5429, KeccakfPermAir.extraction.inter_5428, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5427 c row = (mc 2114 + mc 969 - mc 2168*mc 969 - 2*mc 2114*mc 969 + 2*mc 2114*mc 2168*mc 969) + 2 * KeccakfPermAir.extraction.inter_5425 c row := by
    simp only [KeccakfPermAir.extraction.inter_5427, KeccakfPermAir.extraction.inter_5426, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5425 c row = (mc 2115 + mc 970 - mc 2169*mc 970 - 2*mc 2115*mc 970 + 2*mc 2115*mc 2169*mc 970) + 2 * KeccakfPermAir.extraction.inter_5423 c row := by
    simp only [KeccakfPermAir.extraction.inter_5425, KeccakfPermAir.extraction.inter_5424, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5423 c row = (mc 2116 + mc 971 - mc 2170*mc 971 - 2*mc 2116*mc 971 + 2*mc 2116*mc 2170*mc 971) + 2 * KeccakfPermAir.extraction.inter_5421 c row := by
    simp only [KeccakfPermAir.extraction.inter_5423, KeccakfPermAir.extraction.inter_5422, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5421 c row = (mc 2117 + mc 972 - mc 2171*mc 972 - 2*mc 2117*mc 972 + 2*mc 2117*mc 2171*mc 972) + 2 * KeccakfPermAir.extraction.inter_5419 c row := by
    simp only [KeccakfPermAir.extraction.inter_5421, KeccakfPermAir.extraction.inter_5420, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5419 c row = (mc 2118 + mc 973 - mc 2172*mc 973 - 2*mc 2118*mc 973 + 2*mc 2118*mc 2172*mc 973) + 2 * KeccakfPermAir.extraction.inter_5417 c row := by
    simp only [KeccakfPermAir.extraction.inter_5419, KeccakfPermAir.extraction.inter_5418, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5417 c row = (mc 2119 + mc 974 - mc 2173*mc 974 - 2*mc 2119*mc 974 + 2*mc 2119*mc 2173*mc 974) + 2 * KeccakfPermAir.extraction.inter_5415 c row := by
    simp only [KeccakfPermAir.extraction.inter_5417, KeccakfPermAir.extraction.inter_5416, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5415 c row = (mc 2120 + mc 975 - mc 2174*mc 975 - 2*mc 2120*mc 975 + 2*mc 2120*mc 2174*mc 975) := by
    simp only [KeccakfPermAir.extraction.inter_5415, KeccakfPermAir.extraction.inter_5414, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2965 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2965 c row) :
    ((mc 2121 + mc 976 - mc 2175*mc 976 - 2*mc 2121*mc 976 + 2*mc 2121*mc 2175*mc 976) + 2*(mc 2122 + mc 977 - mc 2176*mc 977 - 2*mc 2122*mc 977 + 2*mc 2122*mc 2176*mc 977) + 4*(mc 2123 + mc 978 - mc 2177*mc 978 - 2*mc 2123*mc 978 + 2*mc 2123*mc 2177*mc 978) + 8*(mc 2124 + mc 979 - mc 2178*mc 979 - 2*mc 2124*mc 979 + 2*mc 2124*mc 2178*mc 979) + 16*(mc 2125 + mc 980 - mc 2179*mc 980 - 2*mc 2125*mc 980 + 2*mc 2125*mc 2179*mc 980) + 32*(mc 2126 + mc 981 - mc 2180*mc 981 - 2*mc 2126*mc 981 + 2*mc 2126*mc 2180*mc 981) + 64*(mc 2127 + mc 982 - mc 2181*mc 982 - 2*mc 2127*mc 982 + 2*mc 2127*mc 2181*mc 982) + 128*(mc 2128 + mc 983 - mc 2182*mc 983 - 2*mc 2128*mc 983 + 2*mc 2128*mc 2182*mc 983) + 256*(mc 2129 + mc 984 - mc 2183*mc 984 - 2*mc 2129*mc 984 + 2*mc 2129*mc 2183*mc 984) + 512*(mc 2130 + mc 985 - mc 2184*mc 985 - 2*mc 2130*mc 985 + 2*mc 2130*mc 2184*mc 985) + 1024*(mc 2131 + mc 986 - mc 2185*mc 986 - 2*mc 2131*mc 986 + 2*mc 2131*mc 2185*mc 986) + 2048*(mc 2132 + mc 987 - mc 2186*mc 987 - 2*mc 2132*mc 987 + 2*mc 2132*mc 2186*mc 987) + 4096*(mc 2133 + mc 988 - mc 2187*mc 988 - 2*mc 2133*mc 988 + 2*mc 2133*mc 2187*mc 988) + 8192*(mc 2134 + mc 989 - mc 2188*mc 989 - 2*mc 2134*mc 989 + 2*mc 2134*mc 2188*mc 989) + 16384*(mc 2135 + mc 990 - mc 2189*mc 990 - 2*mc 2135*mc 990 + 2*mc 2135*mc 2189*mc 990) + 32768*(mc 2136 + mc 991 - mc 2190*mc 991 - 2*mc 2136*mc 991 + 2*mc 2136*mc 2190*mc 991)) - mc 2520 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2965, KeccakfPermAir.extraction.inter_5475, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5474 c row = (mc 2122 + mc 977 - mc 2176*mc 977 - 2*mc 2122*mc 977 + 2*mc 2122*mc 2176*mc 977) + 2 * KeccakfPermAir.extraction.inter_5472 c row := by
    simp only [KeccakfPermAir.extraction.inter_5474, KeccakfPermAir.extraction.inter_5473, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5472 c row = (mc 2123 + mc 978 - mc 2177*mc 978 - 2*mc 2123*mc 978 + 2*mc 2123*mc 2177*mc 978) + 2 * KeccakfPermAir.extraction.inter_5470 c row := by
    simp only [KeccakfPermAir.extraction.inter_5472, KeccakfPermAir.extraction.inter_5471, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5470 c row = (mc 2124 + mc 979 - mc 2178*mc 979 - 2*mc 2124*mc 979 + 2*mc 2124*mc 2178*mc 979) + 2 * KeccakfPermAir.extraction.inter_5468 c row := by
    simp only [KeccakfPermAir.extraction.inter_5470, KeccakfPermAir.extraction.inter_5469, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5468 c row = (mc 2125 + mc 980 - mc 2179*mc 980 - 2*mc 2125*mc 980 + 2*mc 2125*mc 2179*mc 980) + 2 * KeccakfPermAir.extraction.inter_5466 c row := by
    simp only [KeccakfPermAir.extraction.inter_5468, KeccakfPermAir.extraction.inter_5467, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5466 c row = (mc 2126 + mc 981 - mc 2180*mc 981 - 2*mc 2126*mc 981 + 2*mc 2126*mc 2180*mc 981) + 2 * KeccakfPermAir.extraction.inter_5464 c row := by
    simp only [KeccakfPermAir.extraction.inter_5466, KeccakfPermAir.extraction.inter_5465, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5464 c row = (mc 2127 + mc 982 - mc 2181*mc 982 - 2*mc 2127*mc 982 + 2*mc 2127*mc 2181*mc 982) + 2 * KeccakfPermAir.extraction.inter_5462 c row := by
    simp only [KeccakfPermAir.extraction.inter_5464, KeccakfPermAir.extraction.inter_5463, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5462 c row = (mc 2128 + mc 983 - mc 2182*mc 983 - 2*mc 2128*mc 983 + 2*mc 2128*mc 2182*mc 983) + 2 * KeccakfPermAir.extraction.inter_5460 c row := by
    simp only [KeccakfPermAir.extraction.inter_5462, KeccakfPermAir.extraction.inter_5461, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5460 c row = (mc 2129 + mc 984 - mc 2183*mc 984 - 2*mc 2129*mc 984 + 2*mc 2129*mc 2183*mc 984) + 2 * KeccakfPermAir.extraction.inter_5458 c row := by
    simp only [KeccakfPermAir.extraction.inter_5460, KeccakfPermAir.extraction.inter_5459, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5458 c row = (mc 2130 + mc 985 - mc 2184*mc 985 - 2*mc 2130*mc 985 + 2*mc 2130*mc 2184*mc 985) + 2 * KeccakfPermAir.extraction.inter_5456 c row := by
    simp only [KeccakfPermAir.extraction.inter_5458, KeccakfPermAir.extraction.inter_5457, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5456 c row = (mc 2131 + mc 986 - mc 2185*mc 986 - 2*mc 2131*mc 986 + 2*mc 2131*mc 2185*mc 986) + 2 * KeccakfPermAir.extraction.inter_5454 c row := by
    simp only [KeccakfPermAir.extraction.inter_5456, KeccakfPermAir.extraction.inter_5455, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5454 c row = (mc 2132 + mc 987 - mc 2186*mc 987 - 2*mc 2132*mc 987 + 2*mc 2132*mc 2186*mc 987) + 2 * KeccakfPermAir.extraction.inter_5452 c row := by
    simp only [KeccakfPermAir.extraction.inter_5454, KeccakfPermAir.extraction.inter_5453, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5452 c row = (mc 2133 + mc 988 - mc 2187*mc 988 - 2*mc 2133*mc 988 + 2*mc 2133*mc 2187*mc 988) + 2 * KeccakfPermAir.extraction.inter_5450 c row := by
    simp only [KeccakfPermAir.extraction.inter_5452, KeccakfPermAir.extraction.inter_5451, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5450 c row = (mc 2134 + mc 989 - mc 2188*mc 989 - 2*mc 2134*mc 989 + 2*mc 2134*mc 2188*mc 989) + 2 * KeccakfPermAir.extraction.inter_5448 c row := by
    simp only [KeccakfPermAir.extraction.inter_5450, KeccakfPermAir.extraction.inter_5449, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5448 c row = (mc 2135 + mc 990 - mc 2189*mc 990 - 2*mc 2135*mc 990 + 2*mc 2135*mc 2189*mc 990) + 2 * KeccakfPermAir.extraction.inter_5446 c row := by
    simp only [KeccakfPermAir.extraction.inter_5448, KeccakfPermAir.extraction.inter_5447, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5446 c row = (mc 2136 + mc 991 - mc 2190*mc 991 - 2*mc 2136*mc 991 + 2*mc 2136*mc 2190*mc 991) := by
    simp only [KeccakfPermAir.extraction.inter_5446, KeccakfPermAir.extraction.inter_5445, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2966 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2966 c row) :
    ((mc 2191 + mc 1371 - mc 992*mc 1371 - 2*mc 2191*mc 1371 + 2*mc 2191*mc 992*mc 1371) + 2*(mc 2192 + mc 1372 - mc 929*mc 1372 - 2*mc 2192*mc 1372 + 2*mc 2192*mc 929*mc 1372) + 4*(mc 2193 + mc 1373 - mc 930*mc 1373 - 2*mc 2193*mc 1373 + 2*mc 2193*mc 930*mc 1373) + 8*(mc 2194 + mc 1374 - mc 931*mc 1374 - 2*mc 2194*mc 1374 + 2*mc 2194*mc 931*mc 1374) + 16*(mc 2195 + mc 1375 - mc 932*mc 1375 - 2*mc 2195*mc 1375 + 2*mc 2195*mc 932*mc 1375) + 32*(mc 2196 + mc 1376 - mc 933*mc 1376 - 2*mc 2196*mc 1376 + 2*mc 2196*mc 933*mc 1376) + 64*(mc 2197 + mc 1313 - mc 934*mc 1313 - 2*mc 2197*mc 1313 + 2*mc 2197*mc 934*mc 1313) + 128*(mc 2198 + mc 1314 - mc 935*mc 1314 - 2*mc 2198*mc 1314 + 2*mc 2198*mc 935*mc 1314) + 256*(mc 2199 + mc 1315 - mc 936*mc 1315 - 2*mc 2199*mc 1315 + 2*mc 2199*mc 936*mc 1315) + 512*(mc 2200 + mc 1316 - mc 937*mc 1316 - 2*mc 2200*mc 1316 + 2*mc 2200*mc 937*mc 1316) + 1024*(mc 2201 + mc 1317 - mc 938*mc 1317 - 2*mc 2201*mc 1317 + 2*mc 2201*mc 938*mc 1317) + 2048*(mc 2202 + mc 1318 - mc 939*mc 1318 - 2*mc 2202*mc 1318 + 2*mc 2202*mc 939*mc 1318) + 4096*(mc 2203 + mc 1319 - mc 940*mc 1319 - 2*mc 2203*mc 1319 + 2*mc 2203*mc 940*mc 1319) + 8192*(mc 2204 + mc 1320 - mc 941*mc 1320 - 2*mc 2204*mc 1320 + 2*mc 2204*mc 941*mc 1320) + 16384*(mc 2205 + mc 1321 - mc 942*mc 1321 - 2*mc 2205*mc 1321 + 2*mc 2205*mc 942*mc 1321) + 32768*(mc 2206 + mc 1322 - mc 943*mc 1322 - 2*mc 2206*mc 1322 + 2*mc 2206*mc 943*mc 1322)) - mc 2521 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2966, KeccakfPermAir.extraction.inter_5506, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5505 c row = (mc 2192 + mc 1372 - mc 929*mc 1372 - 2*mc 2192*mc 1372 + 2*mc 2192*mc 929*mc 1372) + 2 * KeccakfPermAir.extraction.inter_5503 c row := by
    simp only [KeccakfPermAir.extraction.inter_5505, KeccakfPermAir.extraction.inter_5504, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5503 c row = (mc 2193 + mc 1373 - mc 930*mc 1373 - 2*mc 2193*mc 1373 + 2*mc 2193*mc 930*mc 1373) + 2 * KeccakfPermAir.extraction.inter_5501 c row := by
    simp only [KeccakfPermAir.extraction.inter_5503, KeccakfPermAir.extraction.inter_5502, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5501 c row = (mc 2194 + mc 1374 - mc 931*mc 1374 - 2*mc 2194*mc 1374 + 2*mc 2194*mc 931*mc 1374) + 2 * KeccakfPermAir.extraction.inter_5499 c row := by
    simp only [KeccakfPermAir.extraction.inter_5501, KeccakfPermAir.extraction.inter_5500, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5499 c row = (mc 2195 + mc 1375 - mc 932*mc 1375 - 2*mc 2195*mc 1375 + 2*mc 2195*mc 932*mc 1375) + 2 * KeccakfPermAir.extraction.inter_5497 c row := by
    simp only [KeccakfPermAir.extraction.inter_5499, KeccakfPermAir.extraction.inter_5498, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5497 c row = (mc 2196 + mc 1376 - mc 933*mc 1376 - 2*mc 2196*mc 1376 + 2*mc 2196*mc 933*mc 1376) + 2 * KeccakfPermAir.extraction.inter_5495 c row := by
    simp only [KeccakfPermAir.extraction.inter_5497, KeccakfPermAir.extraction.inter_5496, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5495 c row = (mc 2197 + mc 1313 - mc 934*mc 1313 - 2*mc 2197*mc 1313 + 2*mc 2197*mc 934*mc 1313) + 2 * KeccakfPermAir.extraction.inter_5493 c row := by
    simp only [KeccakfPermAir.extraction.inter_5495, KeccakfPermAir.extraction.inter_5494, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5493 c row = (mc 2198 + mc 1314 - mc 935*mc 1314 - 2*mc 2198*mc 1314 + 2*mc 2198*mc 935*mc 1314) + 2 * KeccakfPermAir.extraction.inter_5491 c row := by
    simp only [KeccakfPermAir.extraction.inter_5493, KeccakfPermAir.extraction.inter_5492, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5491 c row = (mc 2199 + mc 1315 - mc 936*mc 1315 - 2*mc 2199*mc 1315 + 2*mc 2199*mc 936*mc 1315) + 2 * KeccakfPermAir.extraction.inter_5489 c row := by
    simp only [KeccakfPermAir.extraction.inter_5491, KeccakfPermAir.extraction.inter_5490, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5489 c row = (mc 2200 + mc 1316 - mc 937*mc 1316 - 2*mc 2200*mc 1316 + 2*mc 2200*mc 937*mc 1316) + 2 * KeccakfPermAir.extraction.inter_5487 c row := by
    simp only [KeccakfPermAir.extraction.inter_5489, KeccakfPermAir.extraction.inter_5488, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5487 c row = (mc 2201 + mc 1317 - mc 938*mc 1317 - 2*mc 2201*mc 1317 + 2*mc 2201*mc 938*mc 1317) + 2 * KeccakfPermAir.extraction.inter_5485 c row := by
    simp only [KeccakfPermAir.extraction.inter_5487, KeccakfPermAir.extraction.inter_5486, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5485 c row = (mc 2202 + mc 1318 - mc 939*mc 1318 - 2*mc 2202*mc 1318 + 2*mc 2202*mc 939*mc 1318) + 2 * KeccakfPermAir.extraction.inter_5483 c row := by
    simp only [KeccakfPermAir.extraction.inter_5485, KeccakfPermAir.extraction.inter_5484, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5483 c row = (mc 2203 + mc 1319 - mc 940*mc 1319 - 2*mc 2203*mc 1319 + 2*mc 2203*mc 940*mc 1319) + 2 * KeccakfPermAir.extraction.inter_5481 c row := by
    simp only [KeccakfPermAir.extraction.inter_5483, KeccakfPermAir.extraction.inter_5482, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5481 c row = (mc 2204 + mc 1320 - mc 941*mc 1320 - 2*mc 2204*mc 1320 + 2*mc 2204*mc 941*mc 1320) + 2 * KeccakfPermAir.extraction.inter_5479 c row := by
    simp only [KeccakfPermAir.extraction.inter_5481, KeccakfPermAir.extraction.inter_5480, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5479 c row = (mc 2205 + mc 1321 - mc 942*mc 1321 - 2*mc 2205*mc 1321 + 2*mc 2205*mc 942*mc 1321) + 2 * KeccakfPermAir.extraction.inter_5477 c row := by
    simp only [KeccakfPermAir.extraction.inter_5479, KeccakfPermAir.extraction.inter_5478, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5477 c row = (mc 2206 + mc 1322 - mc 943*mc 1322 - 2*mc 2206*mc 1322 + 2*mc 2206*mc 943*mc 1322) := by
    simp only [KeccakfPermAir.extraction.inter_5477, KeccakfPermAir.extraction.inter_5476, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2967 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2967 c row) :
    ((mc 2207 + mc 1323 - mc 944*mc 1323 - 2*mc 2207*mc 1323 + 2*mc 2207*mc 944*mc 1323) + 2*(mc 2208 + mc 1324 - mc 945*mc 1324 - 2*mc 2208*mc 1324 + 2*mc 2208*mc 945*mc 1324) + 4*(mc 2145 + mc 1325 - mc 946*mc 1325 - 2*mc 2145*mc 1325 + 2*mc 2145*mc 946*mc 1325) + 8*(mc 2146 + mc 1326 - mc 947*mc 1326 - 2*mc 2146*mc 1326 + 2*mc 2146*mc 947*mc 1326) + 16*(mc 2147 + mc 1327 - mc 948*mc 1327 - 2*mc 2147*mc 1327 + 2*mc 2147*mc 948*mc 1327) + 32*(mc 2148 + mc 1328 - mc 949*mc 1328 - 2*mc 2148*mc 1328 + 2*mc 2148*mc 949*mc 1328) + 64*(mc 2149 + mc 1329 - mc 950*mc 1329 - 2*mc 2149*mc 1329 + 2*mc 2149*mc 950*mc 1329) + 128*(mc 2150 + mc 1330 - mc 951*mc 1330 - 2*mc 2150*mc 1330 + 2*mc 2150*mc 951*mc 1330) + 256*(mc 2151 + mc 1331 - mc 952*mc 1331 - 2*mc 2151*mc 1331 + 2*mc 2151*mc 952*mc 1331) + 512*(mc 2152 + mc 1332 - mc 953*mc 1332 - 2*mc 2152*mc 1332 + 2*mc 2152*mc 953*mc 1332) + 1024*(mc 2153 + mc 1333 - mc 954*mc 1333 - 2*mc 2153*mc 1333 + 2*mc 2153*mc 954*mc 1333) + 2048*(mc 2154 + mc 1334 - mc 955*mc 1334 - 2*mc 2154*mc 1334 + 2*mc 2154*mc 955*mc 1334) + 4096*(mc 2155 + mc 1335 - mc 956*mc 1335 - 2*mc 2155*mc 1335 + 2*mc 2155*mc 956*mc 1335) + 8192*(mc 2156 + mc 1336 - mc 957*mc 1336 - 2*mc 2156*mc 1336 + 2*mc 2156*mc 957*mc 1336) + 16384*(mc 2157 + mc 1337 - mc 958*mc 1337 - 2*mc 2157*mc 1337 + 2*mc 2157*mc 958*mc 1337) + 32768*(mc 2158 + mc 1338 - mc 959*mc 1338 - 2*mc 2158*mc 1338 + 2*mc 2158*mc 959*mc 1338)) - mc 2522 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2967, KeccakfPermAir.extraction.inter_5537, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5536 c row = (mc 2208 + mc 1324 - mc 945*mc 1324 - 2*mc 2208*mc 1324 + 2*mc 2208*mc 945*mc 1324) + 2 * KeccakfPermAir.extraction.inter_5534 c row := by
    simp only [KeccakfPermAir.extraction.inter_5536, KeccakfPermAir.extraction.inter_5535, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5534 c row = (mc 2145 + mc 1325 - mc 946*mc 1325 - 2*mc 2145*mc 1325 + 2*mc 2145*mc 946*mc 1325) + 2 * KeccakfPermAir.extraction.inter_5532 c row := by
    simp only [KeccakfPermAir.extraction.inter_5534, KeccakfPermAir.extraction.inter_5533, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5532 c row = (mc 2146 + mc 1326 - mc 947*mc 1326 - 2*mc 2146*mc 1326 + 2*mc 2146*mc 947*mc 1326) + 2 * KeccakfPermAir.extraction.inter_5530 c row := by
    simp only [KeccakfPermAir.extraction.inter_5532, KeccakfPermAir.extraction.inter_5531, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5530 c row = (mc 2147 + mc 1327 - mc 948*mc 1327 - 2*mc 2147*mc 1327 + 2*mc 2147*mc 948*mc 1327) + 2 * KeccakfPermAir.extraction.inter_5528 c row := by
    simp only [KeccakfPermAir.extraction.inter_5530, KeccakfPermAir.extraction.inter_5529, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5528 c row = (mc 2148 + mc 1328 - mc 949*mc 1328 - 2*mc 2148*mc 1328 + 2*mc 2148*mc 949*mc 1328) + 2 * KeccakfPermAir.extraction.inter_5526 c row := by
    simp only [KeccakfPermAir.extraction.inter_5528, KeccakfPermAir.extraction.inter_5527, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5526 c row = (mc 2149 + mc 1329 - mc 950*mc 1329 - 2*mc 2149*mc 1329 + 2*mc 2149*mc 950*mc 1329) + 2 * KeccakfPermAir.extraction.inter_5524 c row := by
    simp only [KeccakfPermAir.extraction.inter_5526, KeccakfPermAir.extraction.inter_5525, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5524 c row = (mc 2150 + mc 1330 - mc 951*mc 1330 - 2*mc 2150*mc 1330 + 2*mc 2150*mc 951*mc 1330) + 2 * KeccakfPermAir.extraction.inter_5522 c row := by
    simp only [KeccakfPermAir.extraction.inter_5524, KeccakfPermAir.extraction.inter_5523, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5522 c row = (mc 2151 + mc 1331 - mc 952*mc 1331 - 2*mc 2151*mc 1331 + 2*mc 2151*mc 952*mc 1331) + 2 * KeccakfPermAir.extraction.inter_5520 c row := by
    simp only [KeccakfPermAir.extraction.inter_5522, KeccakfPermAir.extraction.inter_5521, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5520 c row = (mc 2152 + mc 1332 - mc 953*mc 1332 - 2*mc 2152*mc 1332 + 2*mc 2152*mc 953*mc 1332) + 2 * KeccakfPermAir.extraction.inter_5518 c row := by
    simp only [KeccakfPermAir.extraction.inter_5520, KeccakfPermAir.extraction.inter_5519, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5518 c row = (mc 2153 + mc 1333 - mc 954*mc 1333 - 2*mc 2153*mc 1333 + 2*mc 2153*mc 954*mc 1333) + 2 * KeccakfPermAir.extraction.inter_5516 c row := by
    simp only [KeccakfPermAir.extraction.inter_5518, KeccakfPermAir.extraction.inter_5517, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5516 c row = (mc 2154 + mc 1334 - mc 955*mc 1334 - 2*mc 2154*mc 1334 + 2*mc 2154*mc 955*mc 1334) + 2 * KeccakfPermAir.extraction.inter_5514 c row := by
    simp only [KeccakfPermAir.extraction.inter_5516, KeccakfPermAir.extraction.inter_5515, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5514 c row = (mc 2155 + mc 1335 - mc 956*mc 1335 - 2*mc 2155*mc 1335 + 2*mc 2155*mc 956*mc 1335) + 2 * KeccakfPermAir.extraction.inter_5512 c row := by
    simp only [KeccakfPermAir.extraction.inter_5514, KeccakfPermAir.extraction.inter_5513, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5512 c row = (mc 2156 + mc 1336 - mc 957*mc 1336 - 2*mc 2156*mc 1336 + 2*mc 2156*mc 957*mc 1336) + 2 * KeccakfPermAir.extraction.inter_5510 c row := by
    simp only [KeccakfPermAir.extraction.inter_5512, KeccakfPermAir.extraction.inter_5511, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5510 c row = (mc 2157 + mc 1337 - mc 958*mc 1337 - 2*mc 2157*mc 1337 + 2*mc 2157*mc 958*mc 1337) + 2 * KeccakfPermAir.extraction.inter_5508 c row := by
    simp only [KeccakfPermAir.extraction.inter_5510, KeccakfPermAir.extraction.inter_5509, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5508 c row = (mc 2158 + mc 1338 - mc 959*mc 1338 - 2*mc 2158*mc 1338 + 2*mc 2158*mc 959*mc 1338) := by
    simp only [KeccakfPermAir.extraction.inter_5508, KeccakfPermAir.extraction.inter_5507, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2968 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2968 c row) :
    ((mc 2159 + mc 1339 - mc 960*mc 1339 - 2*mc 2159*mc 1339 + 2*mc 2159*mc 960*mc 1339) + 2*(mc 2160 + mc 1340 - mc 961*mc 1340 - 2*mc 2160*mc 1340 + 2*mc 2160*mc 961*mc 1340) + 4*(mc 2161 + mc 1341 - mc 962*mc 1341 - 2*mc 2161*mc 1341 + 2*mc 2161*mc 962*mc 1341) + 8*(mc 2162 + mc 1342 - mc 963*mc 1342 - 2*mc 2162*mc 1342 + 2*mc 2162*mc 963*mc 1342) + 16*(mc 2163 + mc 1343 - mc 964*mc 1343 - 2*mc 2163*mc 1343 + 2*mc 2163*mc 964*mc 1343) + 32*(mc 2164 + mc 1344 - mc 965*mc 1344 - 2*mc 2164*mc 1344 + 2*mc 2164*mc 965*mc 1344) + 64*(mc 2165 + mc 1345 - mc 966*mc 1345 - 2*mc 2165*mc 1345 + 2*mc 2165*mc 966*mc 1345) + 128*(mc 2166 + mc 1346 - mc 967*mc 1346 - 2*mc 2166*mc 1346 + 2*mc 2166*mc 967*mc 1346) + 256*(mc 2167 + mc 1347 - mc 968*mc 1347 - 2*mc 2167*mc 1347 + 2*mc 2167*mc 968*mc 1347) + 512*(mc 2168 + mc 1348 - mc 969*mc 1348 - 2*mc 2168*mc 1348 + 2*mc 2168*mc 969*mc 1348) + 1024*(mc 2169 + mc 1349 - mc 970*mc 1349 - 2*mc 2169*mc 1349 + 2*mc 2169*mc 970*mc 1349) + 2048*(mc 2170 + mc 1350 - mc 971*mc 1350 - 2*mc 2170*mc 1350 + 2*mc 2170*mc 971*mc 1350) + 4096*(mc 2171 + mc 1351 - mc 972*mc 1351 - 2*mc 2171*mc 1351 + 2*mc 2171*mc 972*mc 1351) + 8192*(mc 2172 + mc 1352 - mc 973*mc 1352 - 2*mc 2172*mc 1352 + 2*mc 2172*mc 973*mc 1352) + 16384*(mc 2173 + mc 1353 - mc 974*mc 1353 - 2*mc 2173*mc 1353 + 2*mc 2173*mc 974*mc 1353) + 32768*(mc 2174 + mc 1354 - mc 975*mc 1354 - 2*mc 2174*mc 1354 + 2*mc 2174*mc 975*mc 1354)) - mc 2523 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2968, KeccakfPermAir.extraction.inter_5568, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5567 c row = (mc 2160 + mc 1340 - mc 961*mc 1340 - 2*mc 2160*mc 1340 + 2*mc 2160*mc 961*mc 1340) + 2 * KeccakfPermAir.extraction.inter_5565 c row := by
    simp only [KeccakfPermAir.extraction.inter_5567, KeccakfPermAir.extraction.inter_5566, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5565 c row = (mc 2161 + mc 1341 - mc 962*mc 1341 - 2*mc 2161*mc 1341 + 2*mc 2161*mc 962*mc 1341) + 2 * KeccakfPermAir.extraction.inter_5563 c row := by
    simp only [KeccakfPermAir.extraction.inter_5565, KeccakfPermAir.extraction.inter_5564, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5563 c row = (mc 2162 + mc 1342 - mc 963*mc 1342 - 2*mc 2162*mc 1342 + 2*mc 2162*mc 963*mc 1342) + 2 * KeccakfPermAir.extraction.inter_5561 c row := by
    simp only [KeccakfPermAir.extraction.inter_5563, KeccakfPermAir.extraction.inter_5562, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5561 c row = (mc 2163 + mc 1343 - mc 964*mc 1343 - 2*mc 2163*mc 1343 + 2*mc 2163*mc 964*mc 1343) + 2 * KeccakfPermAir.extraction.inter_5559 c row := by
    simp only [KeccakfPermAir.extraction.inter_5561, KeccakfPermAir.extraction.inter_5560, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5559 c row = (mc 2164 + mc 1344 - mc 965*mc 1344 - 2*mc 2164*mc 1344 + 2*mc 2164*mc 965*mc 1344) + 2 * KeccakfPermAir.extraction.inter_5557 c row := by
    simp only [KeccakfPermAir.extraction.inter_5559, KeccakfPermAir.extraction.inter_5558, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5557 c row = (mc 2165 + mc 1345 - mc 966*mc 1345 - 2*mc 2165*mc 1345 + 2*mc 2165*mc 966*mc 1345) + 2 * KeccakfPermAir.extraction.inter_5555 c row := by
    simp only [KeccakfPermAir.extraction.inter_5557, KeccakfPermAir.extraction.inter_5556, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5555 c row = (mc 2166 + mc 1346 - mc 967*mc 1346 - 2*mc 2166*mc 1346 + 2*mc 2166*mc 967*mc 1346) + 2 * KeccakfPermAir.extraction.inter_5553 c row := by
    simp only [KeccakfPermAir.extraction.inter_5555, KeccakfPermAir.extraction.inter_5554, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5553 c row = (mc 2167 + mc 1347 - mc 968*mc 1347 - 2*mc 2167*mc 1347 + 2*mc 2167*mc 968*mc 1347) + 2 * KeccakfPermAir.extraction.inter_5551 c row := by
    simp only [KeccakfPermAir.extraction.inter_5553, KeccakfPermAir.extraction.inter_5552, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5551 c row = (mc 2168 + mc 1348 - mc 969*mc 1348 - 2*mc 2168*mc 1348 + 2*mc 2168*mc 969*mc 1348) + 2 * KeccakfPermAir.extraction.inter_5549 c row := by
    simp only [KeccakfPermAir.extraction.inter_5551, KeccakfPermAir.extraction.inter_5550, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5549 c row = (mc 2169 + mc 1349 - mc 970*mc 1349 - 2*mc 2169*mc 1349 + 2*mc 2169*mc 970*mc 1349) + 2 * KeccakfPermAir.extraction.inter_5547 c row := by
    simp only [KeccakfPermAir.extraction.inter_5549, KeccakfPermAir.extraction.inter_5548, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5547 c row = (mc 2170 + mc 1350 - mc 971*mc 1350 - 2*mc 2170*mc 1350 + 2*mc 2170*mc 971*mc 1350) + 2 * KeccakfPermAir.extraction.inter_5545 c row := by
    simp only [KeccakfPermAir.extraction.inter_5547, KeccakfPermAir.extraction.inter_5546, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5545 c row = (mc 2171 + mc 1351 - mc 972*mc 1351 - 2*mc 2171*mc 1351 + 2*mc 2171*mc 972*mc 1351) + 2 * KeccakfPermAir.extraction.inter_5543 c row := by
    simp only [KeccakfPermAir.extraction.inter_5545, KeccakfPermAir.extraction.inter_5544, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5543 c row = (mc 2172 + mc 1352 - mc 973*mc 1352 - 2*mc 2172*mc 1352 + 2*mc 2172*mc 973*mc 1352) + 2 * KeccakfPermAir.extraction.inter_5541 c row := by
    simp only [KeccakfPermAir.extraction.inter_5543, KeccakfPermAir.extraction.inter_5542, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5541 c row = (mc 2173 + mc 1353 - mc 974*mc 1353 - 2*mc 2173*mc 1353 + 2*mc 2173*mc 974*mc 1353) + 2 * KeccakfPermAir.extraction.inter_5539 c row := by
    simp only [KeccakfPermAir.extraction.inter_5541, KeccakfPermAir.extraction.inter_5540, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5539 c row = (mc 2174 + mc 1354 - mc 975*mc 1354 - 2*mc 2174*mc 1354 + 2*mc 2174*mc 975*mc 1354) := by
    simp only [KeccakfPermAir.extraction.inter_5539, KeccakfPermAir.extraction.inter_5538, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2969 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2969 c row) :
    ((mc 2175 + mc 1355 - mc 976*mc 1355 - 2*mc 2175*mc 1355 + 2*mc 2175*mc 976*mc 1355) + 2*(mc 2176 + mc 1356 - mc 977*mc 1356 - 2*mc 2176*mc 1356 + 2*mc 2176*mc 977*mc 1356) + 4*(mc 2177 + mc 1357 - mc 978*mc 1357 - 2*mc 2177*mc 1357 + 2*mc 2177*mc 978*mc 1357) + 8*(mc 2178 + mc 1358 - mc 979*mc 1358 - 2*mc 2178*mc 1358 + 2*mc 2178*mc 979*mc 1358) + 16*(mc 2179 + mc 1359 - mc 980*mc 1359 - 2*mc 2179*mc 1359 + 2*mc 2179*mc 980*mc 1359) + 32*(mc 2180 + mc 1360 - mc 981*mc 1360 - 2*mc 2180*mc 1360 + 2*mc 2180*mc 981*mc 1360) + 64*(mc 2181 + mc 1361 - mc 982*mc 1361 - 2*mc 2181*mc 1361 + 2*mc 2181*mc 982*mc 1361) + 128*(mc 2182 + mc 1362 - mc 983*mc 1362 - 2*mc 2182*mc 1362 + 2*mc 2182*mc 983*mc 1362) + 256*(mc 2183 + mc 1363 - mc 984*mc 1363 - 2*mc 2183*mc 1363 + 2*mc 2183*mc 984*mc 1363) + 512*(mc 2184 + mc 1364 - mc 985*mc 1364 - 2*mc 2184*mc 1364 + 2*mc 2184*mc 985*mc 1364) + 1024*(mc 2185 + mc 1365 - mc 986*mc 1365 - 2*mc 2185*mc 1365 + 2*mc 2185*mc 986*mc 1365) + 2048*(mc 2186 + mc 1366 - mc 987*mc 1366 - 2*mc 2186*mc 1366 + 2*mc 2186*mc 987*mc 1366) + 4096*(mc 2187 + mc 1367 - mc 988*mc 1367 - 2*mc 2187*mc 1367 + 2*mc 2187*mc 988*mc 1367) + 8192*(mc 2188 + mc 1368 - mc 989*mc 1368 - 2*mc 2188*mc 1368 + 2*mc 2188*mc 989*mc 1368) + 16384*(mc 2189 + mc 1369 - mc 990*mc 1369 - 2*mc 2189*mc 1369 + 2*mc 2189*mc 990*mc 1369) + 32768*(mc 2190 + mc 1370 - mc 991*mc 1370 - 2*mc 2190*mc 1370 + 2*mc 2190*mc 991*mc 1370)) - mc 2524 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2969, KeccakfPermAir.extraction.inter_5599, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5598 c row = (mc 2176 + mc 1356 - mc 977*mc 1356 - 2*mc 2176*mc 1356 + 2*mc 2176*mc 977*mc 1356) + 2 * KeccakfPermAir.extraction.inter_5596 c row := by
    simp only [KeccakfPermAir.extraction.inter_5598, KeccakfPermAir.extraction.inter_5597, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5596 c row = (mc 2177 + mc 1357 - mc 978*mc 1357 - 2*mc 2177*mc 1357 + 2*mc 2177*mc 978*mc 1357) + 2 * KeccakfPermAir.extraction.inter_5594 c row := by
    simp only [KeccakfPermAir.extraction.inter_5596, KeccakfPermAir.extraction.inter_5595, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5594 c row = (mc 2178 + mc 1358 - mc 979*mc 1358 - 2*mc 2178*mc 1358 + 2*mc 2178*mc 979*mc 1358) + 2 * KeccakfPermAir.extraction.inter_5592 c row := by
    simp only [KeccakfPermAir.extraction.inter_5594, KeccakfPermAir.extraction.inter_5593, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5592 c row = (mc 2179 + mc 1359 - mc 980*mc 1359 - 2*mc 2179*mc 1359 + 2*mc 2179*mc 980*mc 1359) + 2 * KeccakfPermAir.extraction.inter_5590 c row := by
    simp only [KeccakfPermAir.extraction.inter_5592, KeccakfPermAir.extraction.inter_5591, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5590 c row = (mc 2180 + mc 1360 - mc 981*mc 1360 - 2*mc 2180*mc 1360 + 2*mc 2180*mc 981*mc 1360) + 2 * KeccakfPermAir.extraction.inter_5588 c row := by
    simp only [KeccakfPermAir.extraction.inter_5590, KeccakfPermAir.extraction.inter_5589, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5588 c row = (mc 2181 + mc 1361 - mc 982*mc 1361 - 2*mc 2181*mc 1361 + 2*mc 2181*mc 982*mc 1361) + 2 * KeccakfPermAir.extraction.inter_5586 c row := by
    simp only [KeccakfPermAir.extraction.inter_5588, KeccakfPermAir.extraction.inter_5587, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5586 c row = (mc 2182 + mc 1362 - mc 983*mc 1362 - 2*mc 2182*mc 1362 + 2*mc 2182*mc 983*mc 1362) + 2 * KeccakfPermAir.extraction.inter_5584 c row := by
    simp only [KeccakfPermAir.extraction.inter_5586, KeccakfPermAir.extraction.inter_5585, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5584 c row = (mc 2183 + mc 1363 - mc 984*mc 1363 - 2*mc 2183*mc 1363 + 2*mc 2183*mc 984*mc 1363) + 2 * KeccakfPermAir.extraction.inter_5582 c row := by
    simp only [KeccakfPermAir.extraction.inter_5584, KeccakfPermAir.extraction.inter_5583, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5582 c row = (mc 2184 + mc 1364 - mc 985*mc 1364 - 2*mc 2184*mc 1364 + 2*mc 2184*mc 985*mc 1364) + 2 * KeccakfPermAir.extraction.inter_5580 c row := by
    simp only [KeccakfPermAir.extraction.inter_5582, KeccakfPermAir.extraction.inter_5581, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5580 c row = (mc 2185 + mc 1365 - mc 986*mc 1365 - 2*mc 2185*mc 1365 + 2*mc 2185*mc 986*mc 1365) + 2 * KeccakfPermAir.extraction.inter_5578 c row := by
    simp only [KeccakfPermAir.extraction.inter_5580, KeccakfPermAir.extraction.inter_5579, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5578 c row = (mc 2186 + mc 1366 - mc 987*mc 1366 - 2*mc 2186*mc 1366 + 2*mc 2186*mc 987*mc 1366) + 2 * KeccakfPermAir.extraction.inter_5576 c row := by
    simp only [KeccakfPermAir.extraction.inter_5578, KeccakfPermAir.extraction.inter_5577, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5576 c row = (mc 2187 + mc 1367 - mc 988*mc 1367 - 2*mc 2187*mc 1367 + 2*mc 2187*mc 988*mc 1367) + 2 * KeccakfPermAir.extraction.inter_5574 c row := by
    simp only [KeccakfPermAir.extraction.inter_5576, KeccakfPermAir.extraction.inter_5575, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5574 c row = (mc 2188 + mc 1368 - mc 989*mc 1368 - 2*mc 2188*mc 1368 + 2*mc 2188*mc 989*mc 1368) + 2 * KeccakfPermAir.extraction.inter_5572 c row := by
    simp only [KeccakfPermAir.extraction.inter_5574, KeccakfPermAir.extraction.inter_5573, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5572 c row = (mc 2189 + mc 1369 - mc 990*mc 1369 - 2*mc 2189*mc 1369 + 2*mc 2189*mc 990*mc 1369) + 2 * KeccakfPermAir.extraction.inter_5570 c row := by
    simp only [KeccakfPermAir.extraction.inter_5572, KeccakfPermAir.extraction.inter_5571, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5570 c row = (mc 2190 + mc 1370 - mc 991*mc 1370 - 2*mc 2190*mc 1370 + 2*mc 2190*mc 991*mc 1370) := by
    simp only [KeccakfPermAir.extraction.inter_5570, KeccakfPermAir.extraction.inter_5569, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2970 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2970 c row) :
    ((mc 1158 + mc 1623 - mc 1213*mc 1623 - 2*mc 1158*mc 1623 + 2*mc 1158*mc 1213*mc 1623) + 2*(mc 1159 + mc 1624 - mc 1214*mc 1624 - 2*mc 1159*mc 1624 + 2*mc 1159*mc 1214*mc 1624) + 4*(mc 1160 + mc 1625 - mc 1215*mc 1625 - 2*mc 1160*mc 1625 + 2*mc 1160*mc 1215*mc 1625) + 8*(mc 1161 + mc 1626 - mc 1216*mc 1626 - 2*mc 1161*mc 1626 + 2*mc 1161*mc 1216*mc 1626) + 16*(mc 1162 + mc 1627 - mc 1217*mc 1627 - 2*mc 1162*mc 1627 + 2*mc 1162*mc 1217*mc 1627) + 32*(mc 1163 + mc 1628 - mc 1218*mc 1628 - 2*mc 1163*mc 1628 + 2*mc 1163*mc 1218*mc 1628) + 64*(mc 1164 + mc 1629 - mc 1219*mc 1629 - 2*mc 1164*mc 1629 + 2*mc 1164*mc 1219*mc 1629) + 128*(mc 1165 + mc 1630 - mc 1220*mc 1630 - 2*mc 1165*mc 1630 + 2*mc 1165*mc 1220*mc 1630) + 256*(mc 1166 + mc 1631 - mc 1221*mc 1631 - 2*mc 1166*mc 1631 + 2*mc 1166*mc 1221*mc 1631) + 512*(mc 1167 + mc 1632 - mc 1222*mc 1632 - 2*mc 1167*mc 1632 + 2*mc 1167*mc 1222*mc 1632) + 1024*(mc 1168 + mc 1569 - mc 1223*mc 1569 - 2*mc 1168*mc 1569 + 2*mc 1168*mc 1223*mc 1569) + 2048*(mc 1169 + mc 1570 - mc 1224*mc 1570 - 2*mc 1169*mc 1570 + 2*mc 1169*mc 1224*mc 1570) + 4096*(mc 1170 + mc 1571 - mc 1225*mc 1571 - 2*mc 1170*mc 1571 + 2*mc 1170*mc 1225*mc 1571) + 8192*(mc 1171 + mc 1572 - mc 1226*mc 1572 - 2*mc 1171*mc 1572 + 2*mc 1171*mc 1226*mc 1572) + 16384*(mc 1172 + mc 1573 - mc 1227*mc 1573 - 2*mc 1172*mc 1573 + 2*mc 1172*mc 1227*mc 1573) + 32768*(mc 1173 + mc 1574 - mc 1228*mc 1574 - 2*mc 1173*mc 1574 + 2*mc 1173*mc 1228*mc 1574)) - mc 2525 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2970, KeccakfPermAir.extraction.inter_5630, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5629 c row = (mc 1159 + mc 1624 - mc 1214*mc 1624 - 2*mc 1159*mc 1624 + 2*mc 1159*mc 1214*mc 1624) + 2 * KeccakfPermAir.extraction.inter_5627 c row := by
    simp only [KeccakfPermAir.extraction.inter_5629, KeccakfPermAir.extraction.inter_5628, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5627 c row = (mc 1160 + mc 1625 - mc 1215*mc 1625 - 2*mc 1160*mc 1625 + 2*mc 1160*mc 1215*mc 1625) + 2 * KeccakfPermAir.extraction.inter_5625 c row := by
    simp only [KeccakfPermAir.extraction.inter_5627, KeccakfPermAir.extraction.inter_5626, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5625 c row = (mc 1161 + mc 1626 - mc 1216*mc 1626 - 2*mc 1161*mc 1626 + 2*mc 1161*mc 1216*mc 1626) + 2 * KeccakfPermAir.extraction.inter_5623 c row := by
    simp only [KeccakfPermAir.extraction.inter_5625, KeccakfPermAir.extraction.inter_5624, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5623 c row = (mc 1162 + mc 1627 - mc 1217*mc 1627 - 2*mc 1162*mc 1627 + 2*mc 1162*mc 1217*mc 1627) + 2 * KeccakfPermAir.extraction.inter_5621 c row := by
    simp only [KeccakfPermAir.extraction.inter_5623, KeccakfPermAir.extraction.inter_5622, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5621 c row = (mc 1163 + mc 1628 - mc 1218*mc 1628 - 2*mc 1163*mc 1628 + 2*mc 1163*mc 1218*mc 1628) + 2 * KeccakfPermAir.extraction.inter_5619 c row := by
    simp only [KeccakfPermAir.extraction.inter_5621, KeccakfPermAir.extraction.inter_5620, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5619 c row = (mc 1164 + mc 1629 - mc 1219*mc 1629 - 2*mc 1164*mc 1629 + 2*mc 1164*mc 1219*mc 1629) + 2 * KeccakfPermAir.extraction.inter_5617 c row := by
    simp only [KeccakfPermAir.extraction.inter_5619, KeccakfPermAir.extraction.inter_5618, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5617 c row = (mc 1165 + mc 1630 - mc 1220*mc 1630 - 2*mc 1165*mc 1630 + 2*mc 1165*mc 1220*mc 1630) + 2 * KeccakfPermAir.extraction.inter_5615 c row := by
    simp only [KeccakfPermAir.extraction.inter_5617, KeccakfPermAir.extraction.inter_5616, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5615 c row = (mc 1166 + mc 1631 - mc 1221*mc 1631 - 2*mc 1166*mc 1631 + 2*mc 1166*mc 1221*mc 1631) + 2 * KeccakfPermAir.extraction.inter_5613 c row := by
    simp only [KeccakfPermAir.extraction.inter_5615, KeccakfPermAir.extraction.inter_5614, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5613 c row = (mc 1167 + mc 1632 - mc 1222*mc 1632 - 2*mc 1167*mc 1632 + 2*mc 1167*mc 1222*mc 1632) + 2 * KeccakfPermAir.extraction.inter_5611 c row := by
    simp only [KeccakfPermAir.extraction.inter_5613, KeccakfPermAir.extraction.inter_5612, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5611 c row = (mc 1168 + mc 1569 - mc 1223*mc 1569 - 2*mc 1168*mc 1569 + 2*mc 1168*mc 1223*mc 1569) + 2 * KeccakfPermAir.extraction.inter_5609 c row := by
    simp only [KeccakfPermAir.extraction.inter_5611, KeccakfPermAir.extraction.inter_5610, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5609 c row = (mc 1169 + mc 1570 - mc 1224*mc 1570 - 2*mc 1169*mc 1570 + 2*mc 1169*mc 1224*mc 1570) + 2 * KeccakfPermAir.extraction.inter_5607 c row := by
    simp only [KeccakfPermAir.extraction.inter_5609, KeccakfPermAir.extraction.inter_5608, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5607 c row = (mc 1170 + mc 1571 - mc 1225*mc 1571 - 2*mc 1170*mc 1571 + 2*mc 1170*mc 1225*mc 1571) + 2 * KeccakfPermAir.extraction.inter_5605 c row := by
    simp only [KeccakfPermAir.extraction.inter_5607, KeccakfPermAir.extraction.inter_5606, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5605 c row = (mc 1171 + mc 1572 - mc 1226*mc 1572 - 2*mc 1171*mc 1572 + 2*mc 1171*mc 1226*mc 1572) + 2 * KeccakfPermAir.extraction.inter_5603 c row := by
    simp only [KeccakfPermAir.extraction.inter_5605, KeccakfPermAir.extraction.inter_5604, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5603 c row = (mc 1172 + mc 1573 - mc 1227*mc 1573 - 2*mc 1172*mc 1573 + 2*mc 1172*mc 1227*mc 1573) + 2 * KeccakfPermAir.extraction.inter_5601 c row := by
    simp only [KeccakfPermAir.extraction.inter_5603, KeccakfPermAir.extraction.inter_5602, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5601 c row = (mc 1173 + mc 1574 - mc 1228*mc 1574 - 2*mc 1173*mc 1574 + 2*mc 1173*mc 1228*mc 1574) := by
    simp only [KeccakfPermAir.extraction.inter_5601, KeccakfPermAir.extraction.inter_5600, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2971 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2971 c row) :
    ((mc 1174 + mc 1575 - mc 1229*mc 1575 - 2*mc 1174*mc 1575 + 2*mc 1174*mc 1229*mc 1575) + 2*(mc 1175 + mc 1576 - mc 1230*mc 1576 - 2*mc 1175*mc 1576 + 2*mc 1175*mc 1230*mc 1576) + 4*(mc 1176 + mc 1577 - mc 1231*mc 1577 - 2*mc 1176*mc 1577 + 2*mc 1176*mc 1231*mc 1577) + 8*(mc 1177 + mc 1578 - mc 1232*mc 1578 - 2*mc 1177*mc 1578 + 2*mc 1177*mc 1232*mc 1578) + 16*(mc 1178 + mc 1579 - mc 1233*mc 1579 - 2*mc 1178*mc 1579 + 2*mc 1178*mc 1233*mc 1579) + 32*(mc 1179 + mc 1580 - mc 1234*mc 1580 - 2*mc 1179*mc 1580 + 2*mc 1179*mc 1234*mc 1580) + 64*(mc 1180 + mc 1581 - mc 1235*mc 1581 - 2*mc 1180*mc 1581 + 2*mc 1180*mc 1235*mc 1581) + 128*(mc 1181 + mc 1582 - mc 1236*mc 1582 - 2*mc 1181*mc 1582 + 2*mc 1181*mc 1236*mc 1582) + 256*(mc 1182 + mc 1583 - mc 1237*mc 1583 - 2*mc 1182*mc 1583 + 2*mc 1182*mc 1237*mc 1583) + 512*(mc 1183 + mc 1584 - mc 1238*mc 1584 - 2*mc 1183*mc 1584 + 2*mc 1183*mc 1238*mc 1584) + 1024*(mc 1184 + mc 1585 - mc 1239*mc 1585 - 2*mc 1184*mc 1585 + 2*mc 1184*mc 1239*mc 1585) + 2048*(mc 1121 + mc 1586 - mc 1240*mc 1586 - 2*mc 1121*mc 1586 + 2*mc 1121*mc 1240*mc 1586) + 4096*(mc 1122 + mc 1587 - mc 1241*mc 1587 - 2*mc 1122*mc 1587 + 2*mc 1122*mc 1241*mc 1587) + 8192*(mc 1123 + mc 1588 - mc 1242*mc 1588 - 2*mc 1123*mc 1588 + 2*mc 1123*mc 1242*mc 1588) + 16384*(mc 1124 + mc 1589 - mc 1243*mc 1589 - 2*mc 1124*mc 1589 + 2*mc 1124*mc 1243*mc 1589) + 32768*(mc 1125 + mc 1590 - mc 1244*mc 1590 - 2*mc 1125*mc 1590 + 2*mc 1125*mc 1244*mc 1590)) - mc 2526 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2971, KeccakfPermAir.extraction.inter_5661, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5660 c row = (mc 1175 + mc 1576 - mc 1230*mc 1576 - 2*mc 1175*mc 1576 + 2*mc 1175*mc 1230*mc 1576) + 2 * KeccakfPermAir.extraction.inter_5658 c row := by
    simp only [KeccakfPermAir.extraction.inter_5660, KeccakfPermAir.extraction.inter_5659, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5658 c row = (mc 1176 + mc 1577 - mc 1231*mc 1577 - 2*mc 1176*mc 1577 + 2*mc 1176*mc 1231*mc 1577) + 2 * KeccakfPermAir.extraction.inter_5656 c row := by
    simp only [KeccakfPermAir.extraction.inter_5658, KeccakfPermAir.extraction.inter_5657, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5656 c row = (mc 1177 + mc 1578 - mc 1232*mc 1578 - 2*mc 1177*mc 1578 + 2*mc 1177*mc 1232*mc 1578) + 2 * KeccakfPermAir.extraction.inter_5654 c row := by
    simp only [KeccakfPermAir.extraction.inter_5656, KeccakfPermAir.extraction.inter_5655, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5654 c row = (mc 1178 + mc 1579 - mc 1233*mc 1579 - 2*mc 1178*mc 1579 + 2*mc 1178*mc 1233*mc 1579) + 2 * KeccakfPermAir.extraction.inter_5652 c row := by
    simp only [KeccakfPermAir.extraction.inter_5654, KeccakfPermAir.extraction.inter_5653, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5652 c row = (mc 1179 + mc 1580 - mc 1234*mc 1580 - 2*mc 1179*mc 1580 + 2*mc 1179*mc 1234*mc 1580) + 2 * KeccakfPermAir.extraction.inter_5650 c row := by
    simp only [KeccakfPermAir.extraction.inter_5652, KeccakfPermAir.extraction.inter_5651, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5650 c row = (mc 1180 + mc 1581 - mc 1235*mc 1581 - 2*mc 1180*mc 1581 + 2*mc 1180*mc 1235*mc 1581) + 2 * KeccakfPermAir.extraction.inter_5648 c row := by
    simp only [KeccakfPermAir.extraction.inter_5650, KeccakfPermAir.extraction.inter_5649, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5648 c row = (mc 1181 + mc 1582 - mc 1236*mc 1582 - 2*mc 1181*mc 1582 + 2*mc 1181*mc 1236*mc 1582) + 2 * KeccakfPermAir.extraction.inter_5646 c row := by
    simp only [KeccakfPermAir.extraction.inter_5648, KeccakfPermAir.extraction.inter_5647, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5646 c row = (mc 1182 + mc 1583 - mc 1237*mc 1583 - 2*mc 1182*mc 1583 + 2*mc 1182*mc 1237*mc 1583) + 2 * KeccakfPermAir.extraction.inter_5644 c row := by
    simp only [KeccakfPermAir.extraction.inter_5646, KeccakfPermAir.extraction.inter_5645, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5644 c row = (mc 1183 + mc 1584 - mc 1238*mc 1584 - 2*mc 1183*mc 1584 + 2*mc 1183*mc 1238*mc 1584) + 2 * KeccakfPermAir.extraction.inter_5642 c row := by
    simp only [KeccakfPermAir.extraction.inter_5644, KeccakfPermAir.extraction.inter_5643, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5642 c row = (mc 1184 + mc 1585 - mc 1239*mc 1585 - 2*mc 1184*mc 1585 + 2*mc 1184*mc 1239*mc 1585) + 2 * KeccakfPermAir.extraction.inter_5640 c row := by
    simp only [KeccakfPermAir.extraction.inter_5642, KeccakfPermAir.extraction.inter_5641, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5640 c row = (mc 1121 + mc 1586 - mc 1240*mc 1586 - 2*mc 1121*mc 1586 + 2*mc 1121*mc 1240*mc 1586) + 2 * KeccakfPermAir.extraction.inter_5638 c row := by
    simp only [KeccakfPermAir.extraction.inter_5640, KeccakfPermAir.extraction.inter_5639, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5638 c row = (mc 1122 + mc 1587 - mc 1241*mc 1587 - 2*mc 1122*mc 1587 + 2*mc 1122*mc 1241*mc 1587) + 2 * KeccakfPermAir.extraction.inter_5636 c row := by
    simp only [KeccakfPermAir.extraction.inter_5638, KeccakfPermAir.extraction.inter_5637, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5636 c row = (mc 1123 + mc 1588 - mc 1242*mc 1588 - 2*mc 1123*mc 1588 + 2*mc 1123*mc 1242*mc 1588) + 2 * KeccakfPermAir.extraction.inter_5634 c row := by
    simp only [KeccakfPermAir.extraction.inter_5636, KeccakfPermAir.extraction.inter_5635, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5634 c row = (mc 1124 + mc 1589 - mc 1243*mc 1589 - 2*mc 1124*mc 1589 + 2*mc 1124*mc 1243*mc 1589) + 2 * KeccakfPermAir.extraction.inter_5632 c row := by
    simp only [KeccakfPermAir.extraction.inter_5634, KeccakfPermAir.extraction.inter_5633, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5632 c row = (mc 1125 + mc 1590 - mc 1244*mc 1590 - 2*mc 1125*mc 1590 + 2*mc 1125*mc 1244*mc 1590) := by
    simp only [KeccakfPermAir.extraction.inter_5632, KeccakfPermAir.extraction.inter_5631, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2972 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2972 c row) :
    ((mc 1126 + mc 1591 - mc 1245*mc 1591 - 2*mc 1126*mc 1591 + 2*mc 1126*mc 1245*mc 1591) + 2*(mc 1127 + mc 1592 - mc 1246*mc 1592 - 2*mc 1127*mc 1592 + 2*mc 1127*mc 1246*mc 1592) + 4*(mc 1128 + mc 1593 - mc 1247*mc 1593 - 2*mc 1128*mc 1593 + 2*mc 1128*mc 1247*mc 1593) + 8*(mc 1129 + mc 1594 - mc 1248*mc 1594 - 2*mc 1129*mc 1594 + 2*mc 1129*mc 1248*mc 1594) + 16*(mc 1130 + mc 1595 - mc 1185*mc 1595 - 2*mc 1130*mc 1595 + 2*mc 1130*mc 1185*mc 1595) + 32*(mc 1131 + mc 1596 - mc 1186*mc 1596 - 2*mc 1131*mc 1596 + 2*mc 1131*mc 1186*mc 1596) + 64*(mc 1132 + mc 1597 - mc 1187*mc 1597 - 2*mc 1132*mc 1597 + 2*mc 1132*mc 1187*mc 1597) + 128*(mc 1133 + mc 1598 - mc 1188*mc 1598 - 2*mc 1133*mc 1598 + 2*mc 1133*mc 1188*mc 1598) + 256*(mc 1134 + mc 1599 - mc 1189*mc 1599 - 2*mc 1134*mc 1599 + 2*mc 1134*mc 1189*mc 1599) + 512*(mc 1135 + mc 1600 - mc 1190*mc 1600 - 2*mc 1135*mc 1600 + 2*mc 1135*mc 1190*mc 1600) + 1024*(mc 1136 + mc 1601 - mc 1191*mc 1601 - 2*mc 1136*mc 1601 + 2*mc 1136*mc 1191*mc 1601) + 2048*(mc 1137 + mc 1602 - mc 1192*mc 1602 - 2*mc 1137*mc 1602 + 2*mc 1137*mc 1192*mc 1602) + 4096*(mc 1138 + mc 1603 - mc 1193*mc 1603 - 2*mc 1138*mc 1603 + 2*mc 1138*mc 1193*mc 1603) + 8192*(mc 1139 + mc 1604 - mc 1194*mc 1604 - 2*mc 1139*mc 1604 + 2*mc 1139*mc 1194*mc 1604) + 16384*(mc 1140 + mc 1605 - mc 1195*mc 1605 - 2*mc 1140*mc 1605 + 2*mc 1140*mc 1195*mc 1605) + 32768*(mc 1141 + mc 1606 - mc 1196*mc 1606 - 2*mc 1141*mc 1606 + 2*mc 1141*mc 1196*mc 1606)) - mc 2527 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2972, KeccakfPermAir.extraction.inter_5692, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5691 c row = (mc 1127 + mc 1592 - mc 1246*mc 1592 - 2*mc 1127*mc 1592 + 2*mc 1127*mc 1246*mc 1592) + 2 * KeccakfPermAir.extraction.inter_5689 c row := by
    simp only [KeccakfPermAir.extraction.inter_5691, KeccakfPermAir.extraction.inter_5690, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5689 c row = (mc 1128 + mc 1593 - mc 1247*mc 1593 - 2*mc 1128*mc 1593 + 2*mc 1128*mc 1247*mc 1593) + 2 * KeccakfPermAir.extraction.inter_5687 c row := by
    simp only [KeccakfPermAir.extraction.inter_5689, KeccakfPermAir.extraction.inter_5688, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5687 c row = (mc 1129 + mc 1594 - mc 1248*mc 1594 - 2*mc 1129*mc 1594 + 2*mc 1129*mc 1248*mc 1594) + 2 * KeccakfPermAir.extraction.inter_5685 c row := by
    simp only [KeccakfPermAir.extraction.inter_5687, KeccakfPermAir.extraction.inter_5686, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5685 c row = (mc 1130 + mc 1595 - mc 1185*mc 1595 - 2*mc 1130*mc 1595 + 2*mc 1130*mc 1185*mc 1595) + 2 * KeccakfPermAir.extraction.inter_5683 c row := by
    simp only [KeccakfPermAir.extraction.inter_5685, KeccakfPermAir.extraction.inter_5684, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5683 c row = (mc 1131 + mc 1596 - mc 1186*mc 1596 - 2*mc 1131*mc 1596 + 2*mc 1131*mc 1186*mc 1596) + 2 * KeccakfPermAir.extraction.inter_5681 c row := by
    simp only [KeccakfPermAir.extraction.inter_5683, KeccakfPermAir.extraction.inter_5682, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5681 c row = (mc 1132 + mc 1597 - mc 1187*mc 1597 - 2*mc 1132*mc 1597 + 2*mc 1132*mc 1187*mc 1597) + 2 * KeccakfPermAir.extraction.inter_5679 c row := by
    simp only [KeccakfPermAir.extraction.inter_5681, KeccakfPermAir.extraction.inter_5680, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5679 c row = (mc 1133 + mc 1598 - mc 1188*mc 1598 - 2*mc 1133*mc 1598 + 2*mc 1133*mc 1188*mc 1598) + 2 * KeccakfPermAir.extraction.inter_5677 c row := by
    simp only [KeccakfPermAir.extraction.inter_5679, KeccakfPermAir.extraction.inter_5678, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5677 c row = (mc 1134 + mc 1599 - mc 1189*mc 1599 - 2*mc 1134*mc 1599 + 2*mc 1134*mc 1189*mc 1599) + 2 * KeccakfPermAir.extraction.inter_5675 c row := by
    simp only [KeccakfPermAir.extraction.inter_5677, KeccakfPermAir.extraction.inter_5676, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5675 c row = (mc 1135 + mc 1600 - mc 1190*mc 1600 - 2*mc 1135*mc 1600 + 2*mc 1135*mc 1190*mc 1600) + 2 * KeccakfPermAir.extraction.inter_5673 c row := by
    simp only [KeccakfPermAir.extraction.inter_5675, KeccakfPermAir.extraction.inter_5674, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5673 c row = (mc 1136 + mc 1601 - mc 1191*mc 1601 - 2*mc 1136*mc 1601 + 2*mc 1136*mc 1191*mc 1601) + 2 * KeccakfPermAir.extraction.inter_5671 c row := by
    simp only [KeccakfPermAir.extraction.inter_5673, KeccakfPermAir.extraction.inter_5672, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5671 c row = (mc 1137 + mc 1602 - mc 1192*mc 1602 - 2*mc 1137*mc 1602 + 2*mc 1137*mc 1192*mc 1602) + 2 * KeccakfPermAir.extraction.inter_5669 c row := by
    simp only [KeccakfPermAir.extraction.inter_5671, KeccakfPermAir.extraction.inter_5670, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5669 c row = (mc 1138 + mc 1603 - mc 1193*mc 1603 - 2*mc 1138*mc 1603 + 2*mc 1138*mc 1193*mc 1603) + 2 * KeccakfPermAir.extraction.inter_5667 c row := by
    simp only [KeccakfPermAir.extraction.inter_5669, KeccakfPermAir.extraction.inter_5668, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5667 c row = (mc 1139 + mc 1604 - mc 1194*mc 1604 - 2*mc 1139*mc 1604 + 2*mc 1139*mc 1194*mc 1604) + 2 * KeccakfPermAir.extraction.inter_5665 c row := by
    simp only [KeccakfPermAir.extraction.inter_5667, KeccakfPermAir.extraction.inter_5666, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5665 c row = (mc 1140 + mc 1605 - mc 1195*mc 1605 - 2*mc 1140*mc 1605 + 2*mc 1140*mc 1195*mc 1605) + 2 * KeccakfPermAir.extraction.inter_5663 c row := by
    simp only [KeccakfPermAir.extraction.inter_5665, KeccakfPermAir.extraction.inter_5664, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5663 c row = (mc 1141 + mc 1606 - mc 1196*mc 1606 - 2*mc 1141*mc 1606 + 2*mc 1141*mc 1196*mc 1606) := by
    simp only [KeccakfPermAir.extraction.inter_5663, KeccakfPermAir.extraction.inter_5662, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2973 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2973 c row) :
    ((mc 1142 + mc 1607 - mc 1197*mc 1607 - 2*mc 1142*mc 1607 + 2*mc 1142*mc 1197*mc 1607) + 2*(mc 1143 + mc 1608 - mc 1198*mc 1608 - 2*mc 1143*mc 1608 + 2*mc 1143*mc 1198*mc 1608) + 4*(mc 1144 + mc 1609 - mc 1199*mc 1609 - 2*mc 1144*mc 1609 + 2*mc 1144*mc 1199*mc 1609) + 8*(mc 1145 + mc 1610 - mc 1200*mc 1610 - 2*mc 1145*mc 1610 + 2*mc 1145*mc 1200*mc 1610) + 16*(mc 1146 + mc 1611 - mc 1201*mc 1611 - 2*mc 1146*mc 1611 + 2*mc 1146*mc 1201*mc 1611) + 32*(mc 1147 + mc 1612 - mc 1202*mc 1612 - 2*mc 1147*mc 1612 + 2*mc 1147*mc 1202*mc 1612) + 64*(mc 1148 + mc 1613 - mc 1203*mc 1613 - 2*mc 1148*mc 1613 + 2*mc 1148*mc 1203*mc 1613) + 128*(mc 1149 + mc 1614 - mc 1204*mc 1614 - 2*mc 1149*mc 1614 + 2*mc 1149*mc 1204*mc 1614) + 256*(mc 1150 + mc 1615 - mc 1205*mc 1615 - 2*mc 1150*mc 1615 + 2*mc 1150*mc 1205*mc 1615) + 512*(mc 1151 + mc 1616 - mc 1206*mc 1616 - 2*mc 1151*mc 1616 + 2*mc 1151*mc 1206*mc 1616) + 1024*(mc 1152 + mc 1617 - mc 1207*mc 1617 - 2*mc 1152*mc 1617 + 2*mc 1152*mc 1207*mc 1617) + 2048*(mc 1153 + mc 1618 - mc 1208*mc 1618 - 2*mc 1153*mc 1618 + 2*mc 1153*mc 1208*mc 1618) + 4096*(mc 1154 + mc 1619 - mc 1209*mc 1619 - 2*mc 1154*mc 1619 + 2*mc 1154*mc 1209*mc 1619) + 8192*(mc 1155 + mc 1620 - mc 1210*mc 1620 - 2*mc 1155*mc 1620 + 2*mc 1155*mc 1210*mc 1620) + 16384*(mc 1156 + mc 1621 - mc 1211*mc 1621 - 2*mc 1156*mc 1621 + 2*mc 1156*mc 1211*mc 1621) + 32768*(mc 1157 + mc 1622 - mc 1212*mc 1622 - 2*mc 1157*mc 1622 + 2*mc 1157*mc 1212*mc 1622)) - mc 2528 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2973, KeccakfPermAir.extraction.inter_5723, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5722 c row = (mc 1143 + mc 1608 - mc 1198*mc 1608 - 2*mc 1143*mc 1608 + 2*mc 1143*mc 1198*mc 1608) + 2 * KeccakfPermAir.extraction.inter_5720 c row := by
    simp only [KeccakfPermAir.extraction.inter_5722, KeccakfPermAir.extraction.inter_5721, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5720 c row = (mc 1144 + mc 1609 - mc 1199*mc 1609 - 2*mc 1144*mc 1609 + 2*mc 1144*mc 1199*mc 1609) + 2 * KeccakfPermAir.extraction.inter_5718 c row := by
    simp only [KeccakfPermAir.extraction.inter_5720, KeccakfPermAir.extraction.inter_5719, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5718 c row = (mc 1145 + mc 1610 - mc 1200*mc 1610 - 2*mc 1145*mc 1610 + 2*mc 1145*mc 1200*mc 1610) + 2 * KeccakfPermAir.extraction.inter_5716 c row := by
    simp only [KeccakfPermAir.extraction.inter_5718, KeccakfPermAir.extraction.inter_5717, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5716 c row = (mc 1146 + mc 1611 - mc 1201*mc 1611 - 2*mc 1146*mc 1611 + 2*mc 1146*mc 1201*mc 1611) + 2 * KeccakfPermAir.extraction.inter_5714 c row := by
    simp only [KeccakfPermAir.extraction.inter_5716, KeccakfPermAir.extraction.inter_5715, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5714 c row = (mc 1147 + mc 1612 - mc 1202*mc 1612 - 2*mc 1147*mc 1612 + 2*mc 1147*mc 1202*mc 1612) + 2 * KeccakfPermAir.extraction.inter_5712 c row := by
    simp only [KeccakfPermAir.extraction.inter_5714, KeccakfPermAir.extraction.inter_5713, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5712 c row = (mc 1148 + mc 1613 - mc 1203*mc 1613 - 2*mc 1148*mc 1613 + 2*mc 1148*mc 1203*mc 1613) + 2 * KeccakfPermAir.extraction.inter_5710 c row := by
    simp only [KeccakfPermAir.extraction.inter_5712, KeccakfPermAir.extraction.inter_5711, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5710 c row = (mc 1149 + mc 1614 - mc 1204*mc 1614 - 2*mc 1149*mc 1614 + 2*mc 1149*mc 1204*mc 1614) + 2 * KeccakfPermAir.extraction.inter_5708 c row := by
    simp only [KeccakfPermAir.extraction.inter_5710, KeccakfPermAir.extraction.inter_5709, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5708 c row = (mc 1150 + mc 1615 - mc 1205*mc 1615 - 2*mc 1150*mc 1615 + 2*mc 1150*mc 1205*mc 1615) + 2 * KeccakfPermAir.extraction.inter_5706 c row := by
    simp only [KeccakfPermAir.extraction.inter_5708, KeccakfPermAir.extraction.inter_5707, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5706 c row = (mc 1151 + mc 1616 - mc 1206*mc 1616 - 2*mc 1151*mc 1616 + 2*mc 1151*mc 1206*mc 1616) + 2 * KeccakfPermAir.extraction.inter_5704 c row := by
    simp only [KeccakfPermAir.extraction.inter_5706, KeccakfPermAir.extraction.inter_5705, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5704 c row = (mc 1152 + mc 1617 - mc 1207*mc 1617 - 2*mc 1152*mc 1617 + 2*mc 1152*mc 1207*mc 1617) + 2 * KeccakfPermAir.extraction.inter_5702 c row := by
    simp only [KeccakfPermAir.extraction.inter_5704, KeccakfPermAir.extraction.inter_5703, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5702 c row = (mc 1153 + mc 1618 - mc 1208*mc 1618 - 2*mc 1153*mc 1618 + 2*mc 1153*mc 1208*mc 1618) + 2 * KeccakfPermAir.extraction.inter_5700 c row := by
    simp only [KeccakfPermAir.extraction.inter_5702, KeccakfPermAir.extraction.inter_5701, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5700 c row = (mc 1154 + mc 1619 - mc 1209*mc 1619 - 2*mc 1154*mc 1619 + 2*mc 1154*mc 1209*mc 1619) + 2 * KeccakfPermAir.extraction.inter_5698 c row := by
    simp only [KeccakfPermAir.extraction.inter_5700, KeccakfPermAir.extraction.inter_5699, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5698 c row = (mc 1155 + mc 1620 - mc 1210*mc 1620 - 2*mc 1155*mc 1620 + 2*mc 1155*mc 1210*mc 1620) + 2 * KeccakfPermAir.extraction.inter_5696 c row := by
    simp only [KeccakfPermAir.extraction.inter_5698, KeccakfPermAir.extraction.inter_5697, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5696 c row = (mc 1156 + mc 1621 - mc 1211*mc 1621 - 2*mc 1156*mc 1621 + 2*mc 1156*mc 1211*mc 1621) + 2 * KeccakfPermAir.extraction.inter_5694 c row := by
    simp only [KeccakfPermAir.extraction.inter_5696, KeccakfPermAir.extraction.inter_5695, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5694 c row = (mc 1157 + mc 1622 - mc 1212*mc 1622 - 2*mc 1157*mc 1622 + 2*mc 1157*mc 1212*mc 1622) := by
    simp only [KeccakfPermAir.extraction.inter_5694, KeccakfPermAir.extraction.inter_5693, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2974 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2974 c row) :
    ((mc 1213 + mc 2002 - mc 1623*mc 2002 - 2*mc 1213*mc 2002 + 2*mc 1213*mc 1623*mc 2002) + 2*(mc 1214 + mc 2003 - mc 1624*mc 2003 - 2*mc 1214*mc 2003 + 2*mc 1214*mc 1624*mc 2003) + 4*(mc 1215 + mc 2004 - mc 1625*mc 2004 - 2*mc 1215*mc 2004 + 2*mc 1215*mc 1625*mc 2004) + 8*(mc 1216 + mc 2005 - mc 1626*mc 2005 - 2*mc 1216*mc 2005 + 2*mc 1216*mc 1626*mc 2005) + 16*(mc 1217 + mc 2006 - mc 1627*mc 2006 - 2*mc 1217*mc 2006 + 2*mc 1217*mc 1627*mc 2006) + 32*(mc 1218 + mc 2007 - mc 1628*mc 2007 - 2*mc 1218*mc 2007 + 2*mc 1218*mc 1628*mc 2007) + 64*(mc 1219 + mc 2008 - mc 1629*mc 2008 - 2*mc 1219*mc 2008 + 2*mc 1219*mc 1629*mc 2008) + 128*(mc 1220 + mc 2009 - mc 1630*mc 2009 - 2*mc 1220*mc 2009 + 2*mc 1220*mc 1630*mc 2009) + 256*(mc 1221 + mc 2010 - mc 1631*mc 2010 - 2*mc 1221*mc 2010 + 2*mc 1221*mc 1631*mc 2010) + 512*(mc 1222 + mc 2011 - mc 1632*mc 2011 - 2*mc 1222*mc 2011 + 2*mc 1222*mc 1632*mc 2011) + 1024*(mc 1223 + mc 2012 - mc 1569*mc 2012 - 2*mc 1223*mc 2012 + 2*mc 1223*mc 1569*mc 2012) + 2048*(mc 1224 + mc 2013 - mc 1570*mc 2013 - 2*mc 1224*mc 2013 + 2*mc 1224*mc 1570*mc 2013) + 4096*(mc 1225 + mc 2014 - mc 1571*mc 2014 - 2*mc 1225*mc 2014 + 2*mc 1225*mc 1571*mc 2014) + 8192*(mc 1226 + mc 2015 - mc 1572*mc 2015 - 2*mc 1226*mc 2015 + 2*mc 1226*mc 1572*mc 2015) + 16384*(mc 1227 + mc 2016 - mc 1573*mc 2016 - 2*mc 1227*mc 2016 + 2*mc 1227*mc 1573*mc 2016) + 32768*(mc 1228 + mc 1953 - mc 1574*mc 1953 - 2*mc 1228*mc 1953 + 2*mc 1228*mc 1574*mc 1953)) - mc 2529 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2974, KeccakfPermAir.extraction.inter_5754, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5753 c row = (mc 1214 + mc 2003 - mc 1624*mc 2003 - 2*mc 1214*mc 2003 + 2*mc 1214*mc 1624*mc 2003) + 2 * KeccakfPermAir.extraction.inter_5751 c row := by
    simp only [KeccakfPermAir.extraction.inter_5753, KeccakfPermAir.extraction.inter_5752, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5751 c row = (mc 1215 + mc 2004 - mc 1625*mc 2004 - 2*mc 1215*mc 2004 + 2*mc 1215*mc 1625*mc 2004) + 2 * KeccakfPermAir.extraction.inter_5749 c row := by
    simp only [KeccakfPermAir.extraction.inter_5751, KeccakfPermAir.extraction.inter_5750, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5749 c row = (mc 1216 + mc 2005 - mc 1626*mc 2005 - 2*mc 1216*mc 2005 + 2*mc 1216*mc 1626*mc 2005) + 2 * KeccakfPermAir.extraction.inter_5747 c row := by
    simp only [KeccakfPermAir.extraction.inter_5749, KeccakfPermAir.extraction.inter_5748, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5747 c row = (mc 1217 + mc 2006 - mc 1627*mc 2006 - 2*mc 1217*mc 2006 + 2*mc 1217*mc 1627*mc 2006) + 2 * KeccakfPermAir.extraction.inter_5745 c row := by
    simp only [KeccakfPermAir.extraction.inter_5747, KeccakfPermAir.extraction.inter_5746, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5745 c row = (mc 1218 + mc 2007 - mc 1628*mc 2007 - 2*mc 1218*mc 2007 + 2*mc 1218*mc 1628*mc 2007) + 2 * KeccakfPermAir.extraction.inter_5743 c row := by
    simp only [KeccakfPermAir.extraction.inter_5745, KeccakfPermAir.extraction.inter_5744, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5743 c row = (mc 1219 + mc 2008 - mc 1629*mc 2008 - 2*mc 1219*mc 2008 + 2*mc 1219*mc 1629*mc 2008) + 2 * KeccakfPermAir.extraction.inter_5741 c row := by
    simp only [KeccakfPermAir.extraction.inter_5743, KeccakfPermAir.extraction.inter_5742, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5741 c row = (mc 1220 + mc 2009 - mc 1630*mc 2009 - 2*mc 1220*mc 2009 + 2*mc 1220*mc 1630*mc 2009) + 2 * KeccakfPermAir.extraction.inter_5739 c row := by
    simp only [KeccakfPermAir.extraction.inter_5741, KeccakfPermAir.extraction.inter_5740, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5739 c row = (mc 1221 + mc 2010 - mc 1631*mc 2010 - 2*mc 1221*mc 2010 + 2*mc 1221*mc 1631*mc 2010) + 2 * KeccakfPermAir.extraction.inter_5737 c row := by
    simp only [KeccakfPermAir.extraction.inter_5739, KeccakfPermAir.extraction.inter_5738, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5737 c row = (mc 1222 + mc 2011 - mc 1632*mc 2011 - 2*mc 1222*mc 2011 + 2*mc 1222*mc 1632*mc 2011) + 2 * KeccakfPermAir.extraction.inter_5735 c row := by
    simp only [KeccakfPermAir.extraction.inter_5737, KeccakfPermAir.extraction.inter_5736, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5735 c row = (mc 1223 + mc 2012 - mc 1569*mc 2012 - 2*mc 1223*mc 2012 + 2*mc 1223*mc 1569*mc 2012) + 2 * KeccakfPermAir.extraction.inter_5733 c row := by
    simp only [KeccakfPermAir.extraction.inter_5735, KeccakfPermAir.extraction.inter_5734, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5733 c row = (mc 1224 + mc 2013 - mc 1570*mc 2013 - 2*mc 1224*mc 2013 + 2*mc 1224*mc 1570*mc 2013) + 2 * KeccakfPermAir.extraction.inter_5731 c row := by
    simp only [KeccakfPermAir.extraction.inter_5733, KeccakfPermAir.extraction.inter_5732, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5731 c row = (mc 1225 + mc 2014 - mc 1571*mc 2014 - 2*mc 1225*mc 2014 + 2*mc 1225*mc 1571*mc 2014) + 2 * KeccakfPermAir.extraction.inter_5729 c row := by
    simp only [KeccakfPermAir.extraction.inter_5731, KeccakfPermAir.extraction.inter_5730, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5729 c row = (mc 1226 + mc 2015 - mc 1572*mc 2015 - 2*mc 1226*mc 2015 + 2*mc 1226*mc 1572*mc 2015) + 2 * KeccakfPermAir.extraction.inter_5727 c row := by
    simp only [KeccakfPermAir.extraction.inter_5729, KeccakfPermAir.extraction.inter_5728, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5727 c row = (mc 1227 + mc 2016 - mc 1573*mc 2016 - 2*mc 1227*mc 2016 + 2*mc 1227*mc 1573*mc 2016) + 2 * KeccakfPermAir.extraction.inter_5725 c row := by
    simp only [KeccakfPermAir.extraction.inter_5727, KeccakfPermAir.extraction.inter_5726, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5725 c row = (mc 1228 + mc 1953 - mc 1574*mc 1953 - 2*mc 1228*mc 1953 + 2*mc 1228*mc 1574*mc 1953) := by
    simp only [KeccakfPermAir.extraction.inter_5725, KeccakfPermAir.extraction.inter_5724, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2975 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2975 c row) :
    ((mc 1229 + mc 1954 - mc 1575*mc 1954 - 2*mc 1229*mc 1954 + 2*mc 1229*mc 1575*mc 1954) + 2*(mc 1230 + mc 1955 - mc 1576*mc 1955 - 2*mc 1230*mc 1955 + 2*mc 1230*mc 1576*mc 1955) + 4*(mc 1231 + mc 1956 - mc 1577*mc 1956 - 2*mc 1231*mc 1956 + 2*mc 1231*mc 1577*mc 1956) + 8*(mc 1232 + mc 1957 - mc 1578*mc 1957 - 2*mc 1232*mc 1957 + 2*mc 1232*mc 1578*mc 1957) + 16*(mc 1233 + mc 1958 - mc 1579*mc 1958 - 2*mc 1233*mc 1958 + 2*mc 1233*mc 1579*mc 1958) + 32*(mc 1234 + mc 1959 - mc 1580*mc 1959 - 2*mc 1234*mc 1959 + 2*mc 1234*mc 1580*mc 1959) + 64*(mc 1235 + mc 1960 - mc 1581*mc 1960 - 2*mc 1235*mc 1960 + 2*mc 1235*mc 1581*mc 1960) + 128*(mc 1236 + mc 1961 - mc 1582*mc 1961 - 2*mc 1236*mc 1961 + 2*mc 1236*mc 1582*mc 1961) + 256*(mc 1237 + mc 1962 - mc 1583*mc 1962 - 2*mc 1237*mc 1962 + 2*mc 1237*mc 1583*mc 1962) + 512*(mc 1238 + mc 1963 - mc 1584*mc 1963 - 2*mc 1238*mc 1963 + 2*mc 1238*mc 1584*mc 1963) + 1024*(mc 1239 + mc 1964 - mc 1585*mc 1964 - 2*mc 1239*mc 1964 + 2*mc 1239*mc 1585*mc 1964) + 2048*(mc 1240 + mc 1965 - mc 1586*mc 1965 - 2*mc 1240*mc 1965 + 2*mc 1240*mc 1586*mc 1965) + 4096*(mc 1241 + mc 1966 - mc 1587*mc 1966 - 2*mc 1241*mc 1966 + 2*mc 1241*mc 1587*mc 1966) + 8192*(mc 1242 + mc 1967 - mc 1588*mc 1967 - 2*mc 1242*mc 1967 + 2*mc 1242*mc 1588*mc 1967) + 16384*(mc 1243 + mc 1968 - mc 1589*mc 1968 - 2*mc 1243*mc 1968 + 2*mc 1243*mc 1589*mc 1968) + 32768*(mc 1244 + mc 1969 - mc 1590*mc 1969 - 2*mc 1244*mc 1969 + 2*mc 1244*mc 1590*mc 1969)) - mc 2530 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2975, KeccakfPermAir.extraction.inter_5785, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5784 c row = (mc 1230 + mc 1955 - mc 1576*mc 1955 - 2*mc 1230*mc 1955 + 2*mc 1230*mc 1576*mc 1955) + 2 * KeccakfPermAir.extraction.inter_5782 c row := by
    simp only [KeccakfPermAir.extraction.inter_5784, KeccakfPermAir.extraction.inter_5783, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5782 c row = (mc 1231 + mc 1956 - mc 1577*mc 1956 - 2*mc 1231*mc 1956 + 2*mc 1231*mc 1577*mc 1956) + 2 * KeccakfPermAir.extraction.inter_5780 c row := by
    simp only [KeccakfPermAir.extraction.inter_5782, KeccakfPermAir.extraction.inter_5781, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5780 c row = (mc 1232 + mc 1957 - mc 1578*mc 1957 - 2*mc 1232*mc 1957 + 2*mc 1232*mc 1578*mc 1957) + 2 * KeccakfPermAir.extraction.inter_5778 c row := by
    simp only [KeccakfPermAir.extraction.inter_5780, KeccakfPermAir.extraction.inter_5779, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5778 c row = (mc 1233 + mc 1958 - mc 1579*mc 1958 - 2*mc 1233*mc 1958 + 2*mc 1233*mc 1579*mc 1958) + 2 * KeccakfPermAir.extraction.inter_5776 c row := by
    simp only [KeccakfPermAir.extraction.inter_5778, KeccakfPermAir.extraction.inter_5777, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5776 c row = (mc 1234 + mc 1959 - mc 1580*mc 1959 - 2*mc 1234*mc 1959 + 2*mc 1234*mc 1580*mc 1959) + 2 * KeccakfPermAir.extraction.inter_5774 c row := by
    simp only [KeccakfPermAir.extraction.inter_5776, KeccakfPermAir.extraction.inter_5775, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5774 c row = (mc 1235 + mc 1960 - mc 1581*mc 1960 - 2*mc 1235*mc 1960 + 2*mc 1235*mc 1581*mc 1960) + 2 * KeccakfPermAir.extraction.inter_5772 c row := by
    simp only [KeccakfPermAir.extraction.inter_5774, KeccakfPermAir.extraction.inter_5773, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5772 c row = (mc 1236 + mc 1961 - mc 1582*mc 1961 - 2*mc 1236*mc 1961 + 2*mc 1236*mc 1582*mc 1961) + 2 * KeccakfPermAir.extraction.inter_5770 c row := by
    simp only [KeccakfPermAir.extraction.inter_5772, KeccakfPermAir.extraction.inter_5771, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5770 c row = (mc 1237 + mc 1962 - mc 1583*mc 1962 - 2*mc 1237*mc 1962 + 2*mc 1237*mc 1583*mc 1962) + 2 * KeccakfPermAir.extraction.inter_5768 c row := by
    simp only [KeccakfPermAir.extraction.inter_5770, KeccakfPermAir.extraction.inter_5769, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5768 c row = (mc 1238 + mc 1963 - mc 1584*mc 1963 - 2*mc 1238*mc 1963 + 2*mc 1238*mc 1584*mc 1963) + 2 * KeccakfPermAir.extraction.inter_5766 c row := by
    simp only [KeccakfPermAir.extraction.inter_5768, KeccakfPermAir.extraction.inter_5767, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5766 c row = (mc 1239 + mc 1964 - mc 1585*mc 1964 - 2*mc 1239*mc 1964 + 2*mc 1239*mc 1585*mc 1964) + 2 * KeccakfPermAir.extraction.inter_5764 c row := by
    simp only [KeccakfPermAir.extraction.inter_5766, KeccakfPermAir.extraction.inter_5765, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5764 c row = (mc 1240 + mc 1965 - mc 1586*mc 1965 - 2*mc 1240*mc 1965 + 2*mc 1240*mc 1586*mc 1965) + 2 * KeccakfPermAir.extraction.inter_5762 c row := by
    simp only [KeccakfPermAir.extraction.inter_5764, KeccakfPermAir.extraction.inter_5763, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5762 c row = (mc 1241 + mc 1966 - mc 1587*mc 1966 - 2*mc 1241*mc 1966 + 2*mc 1241*mc 1587*mc 1966) + 2 * KeccakfPermAir.extraction.inter_5760 c row := by
    simp only [KeccakfPermAir.extraction.inter_5762, KeccakfPermAir.extraction.inter_5761, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5760 c row = (mc 1242 + mc 1967 - mc 1588*mc 1967 - 2*mc 1242*mc 1967 + 2*mc 1242*mc 1588*mc 1967) + 2 * KeccakfPermAir.extraction.inter_5758 c row := by
    simp only [KeccakfPermAir.extraction.inter_5760, KeccakfPermAir.extraction.inter_5759, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5758 c row = (mc 1243 + mc 1968 - mc 1589*mc 1968 - 2*mc 1243*mc 1968 + 2*mc 1243*mc 1589*mc 1968) + 2 * KeccakfPermAir.extraction.inter_5756 c row := by
    simp only [KeccakfPermAir.extraction.inter_5758, KeccakfPermAir.extraction.inter_5757, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5756 c row = (mc 1244 + mc 1969 - mc 1590*mc 1969 - 2*mc 1244*mc 1969 + 2*mc 1244*mc 1590*mc 1969) := by
    simp only [KeccakfPermAir.extraction.inter_5756, KeccakfPermAir.extraction.inter_5755, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2976 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2976 c row) :
    ((mc 1245 + mc 1970 - mc 1591*mc 1970 - 2*mc 1245*mc 1970 + 2*mc 1245*mc 1591*mc 1970) + 2*(mc 1246 + mc 1971 - mc 1592*mc 1971 - 2*mc 1246*mc 1971 + 2*mc 1246*mc 1592*mc 1971) + 4*(mc 1247 + mc 1972 - mc 1593*mc 1972 - 2*mc 1247*mc 1972 + 2*mc 1247*mc 1593*mc 1972) + 8*(mc 1248 + mc 1973 - mc 1594*mc 1973 - 2*mc 1248*mc 1973 + 2*mc 1248*mc 1594*mc 1973) + 16*(mc 1185 + mc 1974 - mc 1595*mc 1974 - 2*mc 1185*mc 1974 + 2*mc 1185*mc 1595*mc 1974) + 32*(mc 1186 + mc 1975 - mc 1596*mc 1975 - 2*mc 1186*mc 1975 + 2*mc 1186*mc 1596*mc 1975) + 64*(mc 1187 + mc 1976 - mc 1597*mc 1976 - 2*mc 1187*mc 1976 + 2*mc 1187*mc 1597*mc 1976) + 128*(mc 1188 + mc 1977 - mc 1598*mc 1977 - 2*mc 1188*mc 1977 + 2*mc 1188*mc 1598*mc 1977) + 256*(mc 1189 + mc 1978 - mc 1599*mc 1978 - 2*mc 1189*mc 1978 + 2*mc 1189*mc 1599*mc 1978) + 512*(mc 1190 + mc 1979 - mc 1600*mc 1979 - 2*mc 1190*mc 1979 + 2*mc 1190*mc 1600*mc 1979) + 1024*(mc 1191 + mc 1980 - mc 1601*mc 1980 - 2*mc 1191*mc 1980 + 2*mc 1191*mc 1601*mc 1980) + 2048*(mc 1192 + mc 1981 - mc 1602*mc 1981 - 2*mc 1192*mc 1981 + 2*mc 1192*mc 1602*mc 1981) + 4096*(mc 1193 + mc 1982 - mc 1603*mc 1982 - 2*mc 1193*mc 1982 + 2*mc 1193*mc 1603*mc 1982) + 8192*(mc 1194 + mc 1983 - mc 1604*mc 1983 - 2*mc 1194*mc 1983 + 2*mc 1194*mc 1604*mc 1983) + 16384*(mc 1195 + mc 1984 - mc 1605*mc 1984 - 2*mc 1195*mc 1984 + 2*mc 1195*mc 1605*mc 1984) + 32768*(mc 1196 + mc 1985 - mc 1606*mc 1985 - 2*mc 1196*mc 1985 + 2*mc 1196*mc 1606*mc 1985)) - mc 2531 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2976, KeccakfPermAir.extraction.inter_5816, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5815 c row = (mc 1246 + mc 1971 - mc 1592*mc 1971 - 2*mc 1246*mc 1971 + 2*mc 1246*mc 1592*mc 1971) + 2 * KeccakfPermAir.extraction.inter_5813 c row := by
    simp only [KeccakfPermAir.extraction.inter_5815, KeccakfPermAir.extraction.inter_5814, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5813 c row = (mc 1247 + mc 1972 - mc 1593*mc 1972 - 2*mc 1247*mc 1972 + 2*mc 1247*mc 1593*mc 1972) + 2 * KeccakfPermAir.extraction.inter_5811 c row := by
    simp only [KeccakfPermAir.extraction.inter_5813, KeccakfPermAir.extraction.inter_5812, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5811 c row = (mc 1248 + mc 1973 - mc 1594*mc 1973 - 2*mc 1248*mc 1973 + 2*mc 1248*mc 1594*mc 1973) + 2 * KeccakfPermAir.extraction.inter_5809 c row := by
    simp only [KeccakfPermAir.extraction.inter_5811, KeccakfPermAir.extraction.inter_5810, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5809 c row = (mc 1185 + mc 1974 - mc 1595*mc 1974 - 2*mc 1185*mc 1974 + 2*mc 1185*mc 1595*mc 1974) + 2 * KeccakfPermAir.extraction.inter_5807 c row := by
    simp only [KeccakfPermAir.extraction.inter_5809, KeccakfPermAir.extraction.inter_5808, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5807 c row = (mc 1186 + mc 1975 - mc 1596*mc 1975 - 2*mc 1186*mc 1975 + 2*mc 1186*mc 1596*mc 1975) + 2 * KeccakfPermAir.extraction.inter_5805 c row := by
    simp only [KeccakfPermAir.extraction.inter_5807, KeccakfPermAir.extraction.inter_5806, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5805 c row = (mc 1187 + mc 1976 - mc 1597*mc 1976 - 2*mc 1187*mc 1976 + 2*mc 1187*mc 1597*mc 1976) + 2 * KeccakfPermAir.extraction.inter_5803 c row := by
    simp only [KeccakfPermAir.extraction.inter_5805, KeccakfPermAir.extraction.inter_5804, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5803 c row = (mc 1188 + mc 1977 - mc 1598*mc 1977 - 2*mc 1188*mc 1977 + 2*mc 1188*mc 1598*mc 1977) + 2 * KeccakfPermAir.extraction.inter_5801 c row := by
    simp only [KeccakfPermAir.extraction.inter_5803, KeccakfPermAir.extraction.inter_5802, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5801 c row = (mc 1189 + mc 1978 - mc 1599*mc 1978 - 2*mc 1189*mc 1978 + 2*mc 1189*mc 1599*mc 1978) + 2 * KeccakfPermAir.extraction.inter_5799 c row := by
    simp only [KeccakfPermAir.extraction.inter_5801, KeccakfPermAir.extraction.inter_5800, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5799 c row = (mc 1190 + mc 1979 - mc 1600*mc 1979 - 2*mc 1190*mc 1979 + 2*mc 1190*mc 1600*mc 1979) + 2 * KeccakfPermAir.extraction.inter_5797 c row := by
    simp only [KeccakfPermAir.extraction.inter_5799, KeccakfPermAir.extraction.inter_5798, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5797 c row = (mc 1191 + mc 1980 - mc 1601*mc 1980 - 2*mc 1191*mc 1980 + 2*mc 1191*mc 1601*mc 1980) + 2 * KeccakfPermAir.extraction.inter_5795 c row := by
    simp only [KeccakfPermAir.extraction.inter_5797, KeccakfPermAir.extraction.inter_5796, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5795 c row = (mc 1192 + mc 1981 - mc 1602*mc 1981 - 2*mc 1192*mc 1981 + 2*mc 1192*mc 1602*mc 1981) + 2 * KeccakfPermAir.extraction.inter_5793 c row := by
    simp only [KeccakfPermAir.extraction.inter_5795, KeccakfPermAir.extraction.inter_5794, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5793 c row = (mc 1193 + mc 1982 - mc 1603*mc 1982 - 2*mc 1193*mc 1982 + 2*mc 1193*mc 1603*mc 1982) + 2 * KeccakfPermAir.extraction.inter_5791 c row := by
    simp only [KeccakfPermAir.extraction.inter_5793, KeccakfPermAir.extraction.inter_5792, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5791 c row = (mc 1194 + mc 1983 - mc 1604*mc 1983 - 2*mc 1194*mc 1983 + 2*mc 1194*mc 1604*mc 1983) + 2 * KeccakfPermAir.extraction.inter_5789 c row := by
    simp only [KeccakfPermAir.extraction.inter_5791, KeccakfPermAir.extraction.inter_5790, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5789 c row = (mc 1195 + mc 1984 - mc 1605*mc 1984 - 2*mc 1195*mc 1984 + 2*mc 1195*mc 1605*mc 1984) + 2 * KeccakfPermAir.extraction.inter_5787 c row := by
    simp only [KeccakfPermAir.extraction.inter_5789, KeccakfPermAir.extraction.inter_5788, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5787 c row = (mc 1196 + mc 1985 - mc 1606*mc 1985 - 2*mc 1196*mc 1985 + 2*mc 1196*mc 1606*mc 1985) := by
    simp only [KeccakfPermAir.extraction.inter_5787, KeccakfPermAir.extraction.inter_5786, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2977 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2977 c row) :
    ((mc 1197 + mc 1986 - mc 1607*mc 1986 - 2*mc 1197*mc 1986 + 2*mc 1197*mc 1607*mc 1986) + 2*(mc 1198 + mc 1987 - mc 1608*mc 1987 - 2*mc 1198*mc 1987 + 2*mc 1198*mc 1608*mc 1987) + 4*(mc 1199 + mc 1988 - mc 1609*mc 1988 - 2*mc 1199*mc 1988 + 2*mc 1199*mc 1609*mc 1988) + 8*(mc 1200 + mc 1989 - mc 1610*mc 1989 - 2*mc 1200*mc 1989 + 2*mc 1200*mc 1610*mc 1989) + 16*(mc 1201 + mc 1990 - mc 1611*mc 1990 - 2*mc 1201*mc 1990 + 2*mc 1201*mc 1611*mc 1990) + 32*(mc 1202 + mc 1991 - mc 1612*mc 1991 - 2*mc 1202*mc 1991 + 2*mc 1202*mc 1612*mc 1991) + 64*(mc 1203 + mc 1992 - mc 1613*mc 1992 - 2*mc 1203*mc 1992 + 2*mc 1203*mc 1613*mc 1992) + 128*(mc 1204 + mc 1993 - mc 1614*mc 1993 - 2*mc 1204*mc 1993 + 2*mc 1204*mc 1614*mc 1993) + 256*(mc 1205 + mc 1994 - mc 1615*mc 1994 - 2*mc 1205*mc 1994 + 2*mc 1205*mc 1615*mc 1994) + 512*(mc 1206 + mc 1995 - mc 1616*mc 1995 - 2*mc 1206*mc 1995 + 2*mc 1206*mc 1616*mc 1995) + 1024*(mc 1207 + mc 1996 - mc 1617*mc 1996 - 2*mc 1207*mc 1996 + 2*mc 1207*mc 1617*mc 1996) + 2048*(mc 1208 + mc 1997 - mc 1618*mc 1997 - 2*mc 1208*mc 1997 + 2*mc 1208*mc 1618*mc 1997) + 4096*(mc 1209 + mc 1998 - mc 1619*mc 1998 - 2*mc 1209*mc 1998 + 2*mc 1209*mc 1619*mc 1998) + 8192*(mc 1210 + mc 1999 - mc 1620*mc 1999 - 2*mc 1210*mc 1999 + 2*mc 1210*mc 1620*mc 1999) + 16384*(mc 1211 + mc 2000 - mc 1621*mc 2000 - 2*mc 1211*mc 2000 + 2*mc 1211*mc 1621*mc 2000) + 32768*(mc 1212 + mc 2001 - mc 1622*mc 2001 - 2*mc 1212*mc 2001 + 2*mc 1212*mc 1622*mc 2001)) - mc 2532 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2977, KeccakfPermAir.extraction.inter_5847, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5846 c row = (mc 1198 + mc 1987 - mc 1608*mc 1987 - 2*mc 1198*mc 1987 + 2*mc 1198*mc 1608*mc 1987) + 2 * KeccakfPermAir.extraction.inter_5844 c row := by
    simp only [KeccakfPermAir.extraction.inter_5846, KeccakfPermAir.extraction.inter_5845, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5844 c row = (mc 1199 + mc 1988 - mc 1609*mc 1988 - 2*mc 1199*mc 1988 + 2*mc 1199*mc 1609*mc 1988) + 2 * KeccakfPermAir.extraction.inter_5842 c row := by
    simp only [KeccakfPermAir.extraction.inter_5844, KeccakfPermAir.extraction.inter_5843, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5842 c row = (mc 1200 + mc 1989 - mc 1610*mc 1989 - 2*mc 1200*mc 1989 + 2*mc 1200*mc 1610*mc 1989) + 2 * KeccakfPermAir.extraction.inter_5840 c row := by
    simp only [KeccakfPermAir.extraction.inter_5842, KeccakfPermAir.extraction.inter_5841, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5840 c row = (mc 1201 + mc 1990 - mc 1611*mc 1990 - 2*mc 1201*mc 1990 + 2*mc 1201*mc 1611*mc 1990) + 2 * KeccakfPermAir.extraction.inter_5838 c row := by
    simp only [KeccakfPermAir.extraction.inter_5840, KeccakfPermAir.extraction.inter_5839, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5838 c row = (mc 1202 + mc 1991 - mc 1612*mc 1991 - 2*mc 1202*mc 1991 + 2*mc 1202*mc 1612*mc 1991) + 2 * KeccakfPermAir.extraction.inter_5836 c row := by
    simp only [KeccakfPermAir.extraction.inter_5838, KeccakfPermAir.extraction.inter_5837, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5836 c row = (mc 1203 + mc 1992 - mc 1613*mc 1992 - 2*mc 1203*mc 1992 + 2*mc 1203*mc 1613*mc 1992) + 2 * KeccakfPermAir.extraction.inter_5834 c row := by
    simp only [KeccakfPermAir.extraction.inter_5836, KeccakfPermAir.extraction.inter_5835, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5834 c row = (mc 1204 + mc 1993 - mc 1614*mc 1993 - 2*mc 1204*mc 1993 + 2*mc 1204*mc 1614*mc 1993) + 2 * KeccakfPermAir.extraction.inter_5832 c row := by
    simp only [KeccakfPermAir.extraction.inter_5834, KeccakfPermAir.extraction.inter_5833, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5832 c row = (mc 1205 + mc 1994 - mc 1615*mc 1994 - 2*mc 1205*mc 1994 + 2*mc 1205*mc 1615*mc 1994) + 2 * KeccakfPermAir.extraction.inter_5830 c row := by
    simp only [KeccakfPermAir.extraction.inter_5832, KeccakfPermAir.extraction.inter_5831, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5830 c row = (mc 1206 + mc 1995 - mc 1616*mc 1995 - 2*mc 1206*mc 1995 + 2*mc 1206*mc 1616*mc 1995) + 2 * KeccakfPermAir.extraction.inter_5828 c row := by
    simp only [KeccakfPermAir.extraction.inter_5830, KeccakfPermAir.extraction.inter_5829, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5828 c row = (mc 1207 + mc 1996 - mc 1617*mc 1996 - 2*mc 1207*mc 1996 + 2*mc 1207*mc 1617*mc 1996) + 2 * KeccakfPermAir.extraction.inter_5826 c row := by
    simp only [KeccakfPermAir.extraction.inter_5828, KeccakfPermAir.extraction.inter_5827, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5826 c row = (mc 1208 + mc 1997 - mc 1618*mc 1997 - 2*mc 1208*mc 1997 + 2*mc 1208*mc 1618*mc 1997) + 2 * KeccakfPermAir.extraction.inter_5824 c row := by
    simp only [KeccakfPermAir.extraction.inter_5826, KeccakfPermAir.extraction.inter_5825, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5824 c row = (mc 1209 + mc 1998 - mc 1619*mc 1998 - 2*mc 1209*mc 1998 + 2*mc 1209*mc 1619*mc 1998) + 2 * KeccakfPermAir.extraction.inter_5822 c row := by
    simp only [KeccakfPermAir.extraction.inter_5824, KeccakfPermAir.extraction.inter_5823, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5822 c row = (mc 1210 + mc 1999 - mc 1620*mc 1999 - 2*mc 1210*mc 1999 + 2*mc 1210*mc 1620*mc 1999) + 2 * KeccakfPermAir.extraction.inter_5820 c row := by
    simp only [KeccakfPermAir.extraction.inter_5822, KeccakfPermAir.extraction.inter_5821, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5820 c row = (mc 1211 + mc 2000 - mc 1621*mc 2000 - 2*mc 1211*mc 2000 + 2*mc 1211*mc 1621*mc 2000) + 2 * KeccakfPermAir.extraction.inter_5818 c row := by
    simp only [KeccakfPermAir.extraction.inter_5820, KeccakfPermAir.extraction.inter_5819, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5818 c row = (mc 1212 + mc 2001 - mc 1622*mc 2001 - 2*mc 1212*mc 2001 + 2*mc 1212*mc 1622*mc 2001) := by
    simp only [KeccakfPermAir.extraction.inter_5818, KeccakfPermAir.extraction.inter_5817, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2978 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2978 c row) :
    ((mc 1623 + mc 2345 - mc 2002*mc 2345 - 2*mc 1623*mc 2345 + 2*mc 1623*mc 2002*mc 2345) + 2*(mc 1624 + mc 2346 - mc 2003*mc 2346 - 2*mc 1624*mc 2346 + 2*mc 1624*mc 2003*mc 2346) + 4*(mc 1625 + mc 2347 - mc 2004*mc 2347 - 2*mc 1625*mc 2347 + 2*mc 1625*mc 2004*mc 2347) + 8*(mc 1626 + mc 2348 - mc 2005*mc 2348 - 2*mc 1626*mc 2348 + 2*mc 1626*mc 2005*mc 2348) + 16*(mc 1627 + mc 2349 - mc 2006*mc 2349 - 2*mc 1627*mc 2349 + 2*mc 1627*mc 2006*mc 2349) + 32*(mc 1628 + mc 2350 - mc 2007*mc 2350 - 2*mc 1628*mc 2350 + 2*mc 1628*mc 2007*mc 2350) + 64*(mc 1629 + mc 2351 - mc 2008*mc 2351 - 2*mc 1629*mc 2351 + 2*mc 1629*mc 2008*mc 2351) + 128*(mc 1630 + mc 2352 - mc 2009*mc 2352 - 2*mc 1630*mc 2352 + 2*mc 1630*mc 2009*mc 2352) + 256*(mc 1631 + mc 2353 - mc 2010*mc 2353 - 2*mc 1631*mc 2353 + 2*mc 1631*mc 2010*mc 2353) + 512*(mc 1632 + mc 2354 - mc 2011*mc 2354 - 2*mc 1632*mc 2354 + 2*mc 1632*mc 2011*mc 2354) + 1024*(mc 1569 + mc 2355 - mc 2012*mc 2355 - 2*mc 1569*mc 2355 + 2*mc 1569*mc 2012*mc 2355) + 2048*(mc 1570 + mc 2356 - mc 2013*mc 2356 - 2*mc 1570*mc 2356 + 2*mc 1570*mc 2013*mc 2356) + 4096*(mc 1571 + mc 2357 - mc 2014*mc 2357 - 2*mc 1571*mc 2357 + 2*mc 1571*mc 2014*mc 2357) + 8192*(mc 1572 + mc 2358 - mc 2015*mc 2358 - 2*mc 1572*mc 2358 + 2*mc 1572*mc 2015*mc 2358) + 16384*(mc 1573 + mc 2359 - mc 2016*mc 2359 - 2*mc 1573*mc 2359 + 2*mc 1573*mc 2016*mc 2359) + 32768*(mc 1574 + mc 2360 - mc 1953*mc 2360 - 2*mc 1574*mc 2360 + 2*mc 1574*mc 1953*mc 2360)) - mc 2533 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2978, KeccakfPermAir.extraction.inter_5878, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5877 c row = (mc 1624 + mc 2346 - mc 2003*mc 2346 - 2*mc 1624*mc 2346 + 2*mc 1624*mc 2003*mc 2346) + 2 * KeccakfPermAir.extraction.inter_5875 c row := by
    simp only [KeccakfPermAir.extraction.inter_5877, KeccakfPermAir.extraction.inter_5876, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5875 c row = (mc 1625 + mc 2347 - mc 2004*mc 2347 - 2*mc 1625*mc 2347 + 2*mc 1625*mc 2004*mc 2347) + 2 * KeccakfPermAir.extraction.inter_5873 c row := by
    simp only [KeccakfPermAir.extraction.inter_5875, KeccakfPermAir.extraction.inter_5874, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5873 c row = (mc 1626 + mc 2348 - mc 2005*mc 2348 - 2*mc 1626*mc 2348 + 2*mc 1626*mc 2005*mc 2348) + 2 * KeccakfPermAir.extraction.inter_5871 c row := by
    simp only [KeccakfPermAir.extraction.inter_5873, KeccakfPermAir.extraction.inter_5872, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5871 c row = (mc 1627 + mc 2349 - mc 2006*mc 2349 - 2*mc 1627*mc 2349 + 2*mc 1627*mc 2006*mc 2349) + 2 * KeccakfPermAir.extraction.inter_5869 c row := by
    simp only [KeccakfPermAir.extraction.inter_5871, KeccakfPermAir.extraction.inter_5870, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5869 c row = (mc 1628 + mc 2350 - mc 2007*mc 2350 - 2*mc 1628*mc 2350 + 2*mc 1628*mc 2007*mc 2350) + 2 * KeccakfPermAir.extraction.inter_5867 c row := by
    simp only [KeccakfPermAir.extraction.inter_5869, KeccakfPermAir.extraction.inter_5868, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5867 c row = (mc 1629 + mc 2351 - mc 2008*mc 2351 - 2*mc 1629*mc 2351 + 2*mc 1629*mc 2008*mc 2351) + 2 * KeccakfPermAir.extraction.inter_5865 c row := by
    simp only [KeccakfPermAir.extraction.inter_5867, KeccakfPermAir.extraction.inter_5866, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5865 c row = (mc 1630 + mc 2352 - mc 2009*mc 2352 - 2*mc 1630*mc 2352 + 2*mc 1630*mc 2009*mc 2352) + 2 * KeccakfPermAir.extraction.inter_5863 c row := by
    simp only [KeccakfPermAir.extraction.inter_5865, KeccakfPermAir.extraction.inter_5864, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5863 c row = (mc 1631 + mc 2353 - mc 2010*mc 2353 - 2*mc 1631*mc 2353 + 2*mc 1631*mc 2010*mc 2353) + 2 * KeccakfPermAir.extraction.inter_5861 c row := by
    simp only [KeccakfPermAir.extraction.inter_5863, KeccakfPermAir.extraction.inter_5862, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5861 c row = (mc 1632 + mc 2354 - mc 2011*mc 2354 - 2*mc 1632*mc 2354 + 2*mc 1632*mc 2011*mc 2354) + 2 * KeccakfPermAir.extraction.inter_5859 c row := by
    simp only [KeccakfPermAir.extraction.inter_5861, KeccakfPermAir.extraction.inter_5860, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5859 c row = (mc 1569 + mc 2355 - mc 2012*mc 2355 - 2*mc 1569*mc 2355 + 2*mc 1569*mc 2012*mc 2355) + 2 * KeccakfPermAir.extraction.inter_5857 c row := by
    simp only [KeccakfPermAir.extraction.inter_5859, KeccakfPermAir.extraction.inter_5858, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5857 c row = (mc 1570 + mc 2356 - mc 2013*mc 2356 - 2*mc 1570*mc 2356 + 2*mc 1570*mc 2013*mc 2356) + 2 * KeccakfPermAir.extraction.inter_5855 c row := by
    simp only [KeccakfPermAir.extraction.inter_5857, KeccakfPermAir.extraction.inter_5856, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5855 c row = (mc 1571 + mc 2357 - mc 2014*mc 2357 - 2*mc 1571*mc 2357 + 2*mc 1571*mc 2014*mc 2357) + 2 * KeccakfPermAir.extraction.inter_5853 c row := by
    simp only [KeccakfPermAir.extraction.inter_5855, KeccakfPermAir.extraction.inter_5854, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5853 c row = (mc 1572 + mc 2358 - mc 2015*mc 2358 - 2*mc 1572*mc 2358 + 2*mc 1572*mc 2015*mc 2358) + 2 * KeccakfPermAir.extraction.inter_5851 c row := by
    simp only [KeccakfPermAir.extraction.inter_5853, KeccakfPermAir.extraction.inter_5852, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5851 c row = (mc 1573 + mc 2359 - mc 2016*mc 2359 - 2*mc 1573*mc 2359 + 2*mc 1573*mc 2016*mc 2359) + 2 * KeccakfPermAir.extraction.inter_5849 c row := by
    simp only [KeccakfPermAir.extraction.inter_5851, KeccakfPermAir.extraction.inter_5850, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5849 c row = (mc 1574 + mc 2360 - mc 1953*mc 2360 - 2*mc 1574*mc 2360 + 2*mc 1574*mc 1953*mc 2360) := by
    simp only [KeccakfPermAir.extraction.inter_5849, KeccakfPermAir.extraction.inter_5848, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2979 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2979 c row) :
    ((mc 1575 + mc 2361 - mc 1954*mc 2361 - 2*mc 1575*mc 2361 + 2*mc 1575*mc 1954*mc 2361) + 2*(mc 1576 + mc 2362 - mc 1955*mc 2362 - 2*mc 1576*mc 2362 + 2*mc 1576*mc 1955*mc 2362) + 4*(mc 1577 + mc 2363 - mc 1956*mc 2363 - 2*mc 1577*mc 2363 + 2*mc 1577*mc 1956*mc 2363) + 8*(mc 1578 + mc 2364 - mc 1957*mc 2364 - 2*mc 1578*mc 2364 + 2*mc 1578*mc 1957*mc 2364) + 16*(mc 1579 + mc 2365 - mc 1958*mc 2365 - 2*mc 1579*mc 2365 + 2*mc 1579*mc 1958*mc 2365) + 32*(mc 1580 + mc 2366 - mc 1959*mc 2366 - 2*mc 1580*mc 2366 + 2*mc 1580*mc 1959*mc 2366) + 64*(mc 1581 + mc 2367 - mc 1960*mc 2367 - 2*mc 1581*mc 2367 + 2*mc 1581*mc 1960*mc 2367) + 128*(mc 1582 + mc 2368 - mc 1961*mc 2368 - 2*mc 1582*mc 2368 + 2*mc 1582*mc 1961*mc 2368) + 256*(mc 1583 + mc 2369 - mc 1962*mc 2369 - 2*mc 1583*mc 2369 + 2*mc 1583*mc 1962*mc 2369) + 512*(mc 1584 + mc 2370 - mc 1963*mc 2370 - 2*mc 1584*mc 2370 + 2*mc 1584*mc 1963*mc 2370) + 1024*(mc 1585 + mc 2371 - mc 1964*mc 2371 - 2*mc 1585*mc 2371 + 2*mc 1585*mc 1964*mc 2371) + 2048*(mc 1586 + mc 2372 - mc 1965*mc 2372 - 2*mc 1586*mc 2372 + 2*mc 1586*mc 1965*mc 2372) + 4096*(mc 1587 + mc 2373 - mc 1966*mc 2373 - 2*mc 1587*mc 2373 + 2*mc 1587*mc 1966*mc 2373) + 8192*(mc 1588 + mc 2374 - mc 1967*mc 2374 - 2*mc 1588*mc 2374 + 2*mc 1588*mc 1967*mc 2374) + 16384*(mc 1589 + mc 2375 - mc 1968*mc 2375 - 2*mc 1589*mc 2375 + 2*mc 1589*mc 1968*mc 2375) + 32768*(mc 1590 + mc 2376 - mc 1969*mc 2376 - 2*mc 1590*mc 2376 + 2*mc 1590*mc 1969*mc 2376)) - mc 2534 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2979, KeccakfPermAir.extraction.inter_5909, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5908 c row = (mc 1576 + mc 2362 - mc 1955*mc 2362 - 2*mc 1576*mc 2362 + 2*mc 1576*mc 1955*mc 2362) + 2 * KeccakfPermAir.extraction.inter_5906 c row := by
    simp only [KeccakfPermAir.extraction.inter_5908, KeccakfPermAir.extraction.inter_5907, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5906 c row = (mc 1577 + mc 2363 - mc 1956*mc 2363 - 2*mc 1577*mc 2363 + 2*mc 1577*mc 1956*mc 2363) + 2 * KeccakfPermAir.extraction.inter_5904 c row := by
    simp only [KeccakfPermAir.extraction.inter_5906, KeccakfPermAir.extraction.inter_5905, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5904 c row = (mc 1578 + mc 2364 - mc 1957*mc 2364 - 2*mc 1578*mc 2364 + 2*mc 1578*mc 1957*mc 2364) + 2 * KeccakfPermAir.extraction.inter_5902 c row := by
    simp only [KeccakfPermAir.extraction.inter_5904, KeccakfPermAir.extraction.inter_5903, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5902 c row = (mc 1579 + mc 2365 - mc 1958*mc 2365 - 2*mc 1579*mc 2365 + 2*mc 1579*mc 1958*mc 2365) + 2 * KeccakfPermAir.extraction.inter_5900 c row := by
    simp only [KeccakfPermAir.extraction.inter_5902, KeccakfPermAir.extraction.inter_5901, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5900 c row = (mc 1580 + mc 2366 - mc 1959*mc 2366 - 2*mc 1580*mc 2366 + 2*mc 1580*mc 1959*mc 2366) + 2 * KeccakfPermAir.extraction.inter_5898 c row := by
    simp only [KeccakfPermAir.extraction.inter_5900, KeccakfPermAir.extraction.inter_5899, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5898 c row = (mc 1581 + mc 2367 - mc 1960*mc 2367 - 2*mc 1581*mc 2367 + 2*mc 1581*mc 1960*mc 2367) + 2 * KeccakfPermAir.extraction.inter_5896 c row := by
    simp only [KeccakfPermAir.extraction.inter_5898, KeccakfPermAir.extraction.inter_5897, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5896 c row = (mc 1582 + mc 2368 - mc 1961*mc 2368 - 2*mc 1582*mc 2368 + 2*mc 1582*mc 1961*mc 2368) + 2 * KeccakfPermAir.extraction.inter_5894 c row := by
    simp only [KeccakfPermAir.extraction.inter_5896, KeccakfPermAir.extraction.inter_5895, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5894 c row = (mc 1583 + mc 2369 - mc 1962*mc 2369 - 2*mc 1583*mc 2369 + 2*mc 1583*mc 1962*mc 2369) + 2 * KeccakfPermAir.extraction.inter_5892 c row := by
    simp only [KeccakfPermAir.extraction.inter_5894, KeccakfPermAir.extraction.inter_5893, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5892 c row = (mc 1584 + mc 2370 - mc 1963*mc 2370 - 2*mc 1584*mc 2370 + 2*mc 1584*mc 1963*mc 2370) + 2 * KeccakfPermAir.extraction.inter_5890 c row := by
    simp only [KeccakfPermAir.extraction.inter_5892, KeccakfPermAir.extraction.inter_5891, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5890 c row = (mc 1585 + mc 2371 - mc 1964*mc 2371 - 2*mc 1585*mc 2371 + 2*mc 1585*mc 1964*mc 2371) + 2 * KeccakfPermAir.extraction.inter_5888 c row := by
    simp only [KeccakfPermAir.extraction.inter_5890, KeccakfPermAir.extraction.inter_5889, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5888 c row = (mc 1586 + mc 2372 - mc 1965*mc 2372 - 2*mc 1586*mc 2372 + 2*mc 1586*mc 1965*mc 2372) + 2 * KeccakfPermAir.extraction.inter_5886 c row := by
    simp only [KeccakfPermAir.extraction.inter_5888, KeccakfPermAir.extraction.inter_5887, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5886 c row = (mc 1587 + mc 2373 - mc 1966*mc 2373 - 2*mc 1587*mc 2373 + 2*mc 1587*mc 1966*mc 2373) + 2 * KeccakfPermAir.extraction.inter_5884 c row := by
    simp only [KeccakfPermAir.extraction.inter_5886, KeccakfPermAir.extraction.inter_5885, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5884 c row = (mc 1588 + mc 2374 - mc 1967*mc 2374 - 2*mc 1588*mc 2374 + 2*mc 1588*mc 1967*mc 2374) + 2 * KeccakfPermAir.extraction.inter_5882 c row := by
    simp only [KeccakfPermAir.extraction.inter_5884, KeccakfPermAir.extraction.inter_5883, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5882 c row = (mc 1589 + mc 2375 - mc 1968*mc 2375 - 2*mc 1589*mc 2375 + 2*mc 1589*mc 1968*mc 2375) + 2 * KeccakfPermAir.extraction.inter_5880 c row := by
    simp only [KeccakfPermAir.extraction.inter_5882, KeccakfPermAir.extraction.inter_5881, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5880 c row = (mc 1590 + mc 2376 - mc 1969*mc 2376 - 2*mc 1590*mc 2376 + 2*mc 1590*mc 1969*mc 2376) := by
    simp only [KeccakfPermAir.extraction.inter_5880, KeccakfPermAir.extraction.inter_5879, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2980 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2980 c row) :
    ((mc 1591 + mc 2377 - mc 1970*mc 2377 - 2*mc 1591*mc 2377 + 2*mc 1591*mc 1970*mc 2377) + 2*(mc 1592 + mc 2378 - mc 1971*mc 2378 - 2*mc 1592*mc 2378 + 2*mc 1592*mc 1971*mc 2378) + 4*(mc 1593 + mc 2379 - mc 1972*mc 2379 - 2*mc 1593*mc 2379 + 2*mc 1593*mc 1972*mc 2379) + 8*(mc 1594 + mc 2380 - mc 1973*mc 2380 - 2*mc 1594*mc 2380 + 2*mc 1594*mc 1973*mc 2380) + 16*(mc 1595 + mc 2381 - mc 1974*mc 2381 - 2*mc 1595*mc 2381 + 2*mc 1595*mc 1974*mc 2381) + 32*(mc 1596 + mc 2382 - mc 1975*mc 2382 - 2*mc 1596*mc 2382 + 2*mc 1596*mc 1975*mc 2382) + 64*(mc 1597 + mc 2383 - mc 1976*mc 2383 - 2*mc 1597*mc 2383 + 2*mc 1597*mc 1976*mc 2383) + 128*(mc 1598 + mc 2384 - mc 1977*mc 2384 - 2*mc 1598*mc 2384 + 2*mc 1598*mc 1977*mc 2384) + 256*(mc 1599 + mc 2385 - mc 1978*mc 2385 - 2*mc 1599*mc 2385 + 2*mc 1599*mc 1978*mc 2385) + 512*(mc 1600 + mc 2386 - mc 1979*mc 2386 - 2*mc 1600*mc 2386 + 2*mc 1600*mc 1979*mc 2386) + 1024*(mc 1601 + mc 2387 - mc 1980*mc 2387 - 2*mc 1601*mc 2387 + 2*mc 1601*mc 1980*mc 2387) + 2048*(mc 1602 + mc 2388 - mc 1981*mc 2388 - 2*mc 1602*mc 2388 + 2*mc 1602*mc 1981*mc 2388) + 4096*(mc 1603 + mc 2389 - mc 1982*mc 2389 - 2*mc 1603*mc 2389 + 2*mc 1603*mc 1982*mc 2389) + 8192*(mc 1604 + mc 2390 - mc 1983*mc 2390 - 2*mc 1604*mc 2390 + 2*mc 1604*mc 1983*mc 2390) + 16384*(mc 1605 + mc 2391 - mc 1984*mc 2391 - 2*mc 1605*mc 2391 + 2*mc 1605*mc 1984*mc 2391) + 32768*(mc 1606 + mc 2392 - mc 1985*mc 2392 - 2*mc 1606*mc 2392 + 2*mc 1606*mc 1985*mc 2392)) - mc 2535 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2980, KeccakfPermAir.extraction.inter_5940, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5939 c row = (mc 1592 + mc 2378 - mc 1971*mc 2378 - 2*mc 1592*mc 2378 + 2*mc 1592*mc 1971*mc 2378) + 2 * KeccakfPermAir.extraction.inter_5937 c row := by
    simp only [KeccakfPermAir.extraction.inter_5939, KeccakfPermAir.extraction.inter_5938, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5937 c row = (mc 1593 + mc 2379 - mc 1972*mc 2379 - 2*mc 1593*mc 2379 + 2*mc 1593*mc 1972*mc 2379) + 2 * KeccakfPermAir.extraction.inter_5935 c row := by
    simp only [KeccakfPermAir.extraction.inter_5937, KeccakfPermAir.extraction.inter_5936, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5935 c row = (mc 1594 + mc 2380 - mc 1973*mc 2380 - 2*mc 1594*mc 2380 + 2*mc 1594*mc 1973*mc 2380) + 2 * KeccakfPermAir.extraction.inter_5933 c row := by
    simp only [KeccakfPermAir.extraction.inter_5935, KeccakfPermAir.extraction.inter_5934, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5933 c row = (mc 1595 + mc 2381 - mc 1974*mc 2381 - 2*mc 1595*mc 2381 + 2*mc 1595*mc 1974*mc 2381) + 2 * KeccakfPermAir.extraction.inter_5931 c row := by
    simp only [KeccakfPermAir.extraction.inter_5933, KeccakfPermAir.extraction.inter_5932, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5931 c row = (mc 1596 + mc 2382 - mc 1975*mc 2382 - 2*mc 1596*mc 2382 + 2*mc 1596*mc 1975*mc 2382) + 2 * KeccakfPermAir.extraction.inter_5929 c row := by
    simp only [KeccakfPermAir.extraction.inter_5931, KeccakfPermAir.extraction.inter_5930, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5929 c row = (mc 1597 + mc 2383 - mc 1976*mc 2383 - 2*mc 1597*mc 2383 + 2*mc 1597*mc 1976*mc 2383) + 2 * KeccakfPermAir.extraction.inter_5927 c row := by
    simp only [KeccakfPermAir.extraction.inter_5929, KeccakfPermAir.extraction.inter_5928, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5927 c row = (mc 1598 + mc 2384 - mc 1977*mc 2384 - 2*mc 1598*mc 2384 + 2*mc 1598*mc 1977*mc 2384) + 2 * KeccakfPermAir.extraction.inter_5925 c row := by
    simp only [KeccakfPermAir.extraction.inter_5927, KeccakfPermAir.extraction.inter_5926, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5925 c row = (mc 1599 + mc 2385 - mc 1978*mc 2385 - 2*mc 1599*mc 2385 + 2*mc 1599*mc 1978*mc 2385) + 2 * KeccakfPermAir.extraction.inter_5923 c row := by
    simp only [KeccakfPermAir.extraction.inter_5925, KeccakfPermAir.extraction.inter_5924, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5923 c row = (mc 1600 + mc 2386 - mc 1979*mc 2386 - 2*mc 1600*mc 2386 + 2*mc 1600*mc 1979*mc 2386) + 2 * KeccakfPermAir.extraction.inter_5921 c row := by
    simp only [KeccakfPermAir.extraction.inter_5923, KeccakfPermAir.extraction.inter_5922, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5921 c row = (mc 1601 + mc 2387 - mc 1980*mc 2387 - 2*mc 1601*mc 2387 + 2*mc 1601*mc 1980*mc 2387) + 2 * KeccakfPermAir.extraction.inter_5919 c row := by
    simp only [KeccakfPermAir.extraction.inter_5921, KeccakfPermAir.extraction.inter_5920, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5919 c row = (mc 1602 + mc 2388 - mc 1981*mc 2388 - 2*mc 1602*mc 2388 + 2*mc 1602*mc 1981*mc 2388) + 2 * KeccakfPermAir.extraction.inter_5917 c row := by
    simp only [KeccakfPermAir.extraction.inter_5919, KeccakfPermAir.extraction.inter_5918, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5917 c row = (mc 1603 + mc 2389 - mc 1982*mc 2389 - 2*mc 1603*mc 2389 + 2*mc 1603*mc 1982*mc 2389) + 2 * KeccakfPermAir.extraction.inter_5915 c row := by
    simp only [KeccakfPermAir.extraction.inter_5917, KeccakfPermAir.extraction.inter_5916, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5915 c row = (mc 1604 + mc 2390 - mc 1983*mc 2390 - 2*mc 1604*mc 2390 + 2*mc 1604*mc 1983*mc 2390) + 2 * KeccakfPermAir.extraction.inter_5913 c row := by
    simp only [KeccakfPermAir.extraction.inter_5915, KeccakfPermAir.extraction.inter_5914, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5913 c row = (mc 1605 + mc 2391 - mc 1984*mc 2391 - 2*mc 1605*mc 2391 + 2*mc 1605*mc 1984*mc 2391) + 2 * KeccakfPermAir.extraction.inter_5911 c row := by
    simp only [KeccakfPermAir.extraction.inter_5913, KeccakfPermAir.extraction.inter_5912, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5911 c row = (mc 1606 + mc 2392 - mc 1985*mc 2392 - 2*mc 1606*mc 2392 + 2*mc 1606*mc 1985*mc 2392) := by
    simp only [KeccakfPermAir.extraction.inter_5911, KeccakfPermAir.extraction.inter_5910, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2981 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2981 c row) :
    ((mc 1607 + mc 2393 - mc 1986*mc 2393 - 2*mc 1607*mc 2393 + 2*mc 1607*mc 1986*mc 2393) + 2*(mc 1608 + mc 2394 - mc 1987*mc 2394 - 2*mc 1608*mc 2394 + 2*mc 1608*mc 1987*mc 2394) + 4*(mc 1609 + mc 2395 - mc 1988*mc 2395 - 2*mc 1609*mc 2395 + 2*mc 1609*mc 1988*mc 2395) + 8*(mc 1610 + mc 2396 - mc 1989*mc 2396 - 2*mc 1610*mc 2396 + 2*mc 1610*mc 1989*mc 2396) + 16*(mc 1611 + mc 2397 - mc 1990*mc 2397 - 2*mc 1611*mc 2397 + 2*mc 1611*mc 1990*mc 2397) + 32*(mc 1612 + mc 2398 - mc 1991*mc 2398 - 2*mc 1612*mc 2398 + 2*mc 1612*mc 1991*mc 2398) + 64*(mc 1613 + mc 2399 - mc 1992*mc 2399 - 2*mc 1613*mc 2399 + 2*mc 1613*mc 1992*mc 2399) + 128*(mc 1614 + mc 2400 - mc 1993*mc 2400 - 2*mc 1614*mc 2400 + 2*mc 1614*mc 1993*mc 2400) + 256*(mc 1615 + mc 2337 - mc 1994*mc 2337 - 2*mc 1615*mc 2337 + 2*mc 1615*mc 1994*mc 2337) + 512*(mc 1616 + mc 2338 - mc 1995*mc 2338 - 2*mc 1616*mc 2338 + 2*mc 1616*mc 1995*mc 2338) + 1024*(mc 1617 + mc 2339 - mc 1996*mc 2339 - 2*mc 1617*mc 2339 + 2*mc 1617*mc 1996*mc 2339) + 2048*(mc 1618 + mc 2340 - mc 1997*mc 2340 - 2*mc 1618*mc 2340 + 2*mc 1618*mc 1997*mc 2340) + 4096*(mc 1619 + mc 2341 - mc 1998*mc 2341 - 2*mc 1619*mc 2341 + 2*mc 1619*mc 1998*mc 2341) + 8192*(mc 1620 + mc 2342 - mc 1999*mc 2342 - 2*mc 1620*mc 2342 + 2*mc 1620*mc 1999*mc 2342) + 16384*(mc 1621 + mc 2343 - mc 2000*mc 2343 - 2*mc 1621*mc 2343 + 2*mc 1621*mc 2000*mc 2343) + 32768*(mc 1622 + mc 2344 - mc 2001*mc 2344 - 2*mc 1622*mc 2344 + 2*mc 1622*mc 2001*mc 2344)) - mc 2536 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2981, KeccakfPermAir.extraction.inter_5971, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_5970 c row = (mc 1608 + mc 2394 - mc 1987*mc 2394 - 2*mc 1608*mc 2394 + 2*mc 1608*mc 1987*mc 2394) + 2 * KeccakfPermAir.extraction.inter_5968 c row := by
    simp only [KeccakfPermAir.extraction.inter_5970, KeccakfPermAir.extraction.inter_5969, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5968 c row = (mc 1609 + mc 2395 - mc 1988*mc 2395 - 2*mc 1609*mc 2395 + 2*mc 1609*mc 1988*mc 2395) + 2 * KeccakfPermAir.extraction.inter_5966 c row := by
    simp only [KeccakfPermAir.extraction.inter_5968, KeccakfPermAir.extraction.inter_5967, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5966 c row = (mc 1610 + mc 2396 - mc 1989*mc 2396 - 2*mc 1610*mc 2396 + 2*mc 1610*mc 1989*mc 2396) + 2 * KeccakfPermAir.extraction.inter_5964 c row := by
    simp only [KeccakfPermAir.extraction.inter_5966, KeccakfPermAir.extraction.inter_5965, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5964 c row = (mc 1611 + mc 2397 - mc 1990*mc 2397 - 2*mc 1611*mc 2397 + 2*mc 1611*mc 1990*mc 2397) + 2 * KeccakfPermAir.extraction.inter_5962 c row := by
    simp only [KeccakfPermAir.extraction.inter_5964, KeccakfPermAir.extraction.inter_5963, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5962 c row = (mc 1612 + mc 2398 - mc 1991*mc 2398 - 2*mc 1612*mc 2398 + 2*mc 1612*mc 1991*mc 2398) + 2 * KeccakfPermAir.extraction.inter_5960 c row := by
    simp only [KeccakfPermAir.extraction.inter_5962, KeccakfPermAir.extraction.inter_5961, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5960 c row = (mc 1613 + mc 2399 - mc 1992*mc 2399 - 2*mc 1613*mc 2399 + 2*mc 1613*mc 1992*mc 2399) + 2 * KeccakfPermAir.extraction.inter_5958 c row := by
    simp only [KeccakfPermAir.extraction.inter_5960, KeccakfPermAir.extraction.inter_5959, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5958 c row = (mc 1614 + mc 2400 - mc 1993*mc 2400 - 2*mc 1614*mc 2400 + 2*mc 1614*mc 1993*mc 2400) + 2 * KeccakfPermAir.extraction.inter_5956 c row := by
    simp only [KeccakfPermAir.extraction.inter_5958, KeccakfPermAir.extraction.inter_5957, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5956 c row = (mc 1615 + mc 2337 - mc 1994*mc 2337 - 2*mc 1615*mc 2337 + 2*mc 1615*mc 1994*mc 2337) + 2 * KeccakfPermAir.extraction.inter_5954 c row := by
    simp only [KeccakfPermAir.extraction.inter_5956, KeccakfPermAir.extraction.inter_5955, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5954 c row = (mc 1616 + mc 2338 - mc 1995*mc 2338 - 2*mc 1616*mc 2338 + 2*mc 1616*mc 1995*mc 2338) + 2 * KeccakfPermAir.extraction.inter_5952 c row := by
    simp only [KeccakfPermAir.extraction.inter_5954, KeccakfPermAir.extraction.inter_5953, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5952 c row = (mc 1617 + mc 2339 - mc 1996*mc 2339 - 2*mc 1617*mc 2339 + 2*mc 1617*mc 1996*mc 2339) + 2 * KeccakfPermAir.extraction.inter_5950 c row := by
    simp only [KeccakfPermAir.extraction.inter_5952, KeccakfPermAir.extraction.inter_5951, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5950 c row = (mc 1618 + mc 2340 - mc 1997*mc 2340 - 2*mc 1618*mc 2340 + 2*mc 1618*mc 1997*mc 2340) + 2 * KeccakfPermAir.extraction.inter_5948 c row := by
    simp only [KeccakfPermAir.extraction.inter_5950, KeccakfPermAir.extraction.inter_5949, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5948 c row = (mc 1619 + mc 2341 - mc 1998*mc 2341 - 2*mc 1619*mc 2341 + 2*mc 1619*mc 1998*mc 2341) + 2 * KeccakfPermAir.extraction.inter_5946 c row := by
    simp only [KeccakfPermAir.extraction.inter_5948, KeccakfPermAir.extraction.inter_5947, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5946 c row = (mc 1620 + mc 2342 - mc 1999*mc 2342 - 2*mc 1620*mc 2342 + 2*mc 1620*mc 1999*mc 2342) + 2 * KeccakfPermAir.extraction.inter_5944 c row := by
    simp only [KeccakfPermAir.extraction.inter_5946, KeccakfPermAir.extraction.inter_5945, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5944 c row = (mc 1621 + mc 2343 - mc 2000*mc 2343 - 2*mc 1621*mc 2343 + 2*mc 1621*mc 2000*mc 2343) + 2 * KeccakfPermAir.extraction.inter_5942 c row := by
    simp only [KeccakfPermAir.extraction.inter_5944, KeccakfPermAir.extraction.inter_5943, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5942 c row = (mc 1622 + mc 2344 - mc 2001*mc 2344 - 2*mc 1622*mc 2344 + 2*mc 1622*mc 2001*mc 2344) := by
    simp only [KeccakfPermAir.extraction.inter_5942, KeccakfPermAir.extraction.inter_5941, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2982 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2982 c row) :
    ((mc 2002 + mc 1158 - mc 2345*mc 1158 - 2*mc 2002*mc 1158 + 2*mc 2002*mc 2345*mc 1158) + 2*(mc 2003 + mc 1159 - mc 2346*mc 1159 - 2*mc 2003*mc 1159 + 2*mc 2003*mc 2346*mc 1159) + 4*(mc 2004 + mc 1160 - mc 2347*mc 1160 - 2*mc 2004*mc 1160 + 2*mc 2004*mc 2347*mc 1160) + 8*(mc 2005 + mc 1161 - mc 2348*mc 1161 - 2*mc 2005*mc 1161 + 2*mc 2005*mc 2348*mc 1161) + 16*(mc 2006 + mc 1162 - mc 2349*mc 1162 - 2*mc 2006*mc 1162 + 2*mc 2006*mc 2349*mc 1162) + 32*(mc 2007 + mc 1163 - mc 2350*mc 1163 - 2*mc 2007*mc 1163 + 2*mc 2007*mc 2350*mc 1163) + 64*(mc 2008 + mc 1164 - mc 2351*mc 1164 - 2*mc 2008*mc 1164 + 2*mc 2008*mc 2351*mc 1164) + 128*(mc 2009 + mc 1165 - mc 2352*mc 1165 - 2*mc 2009*mc 1165 + 2*mc 2009*mc 2352*mc 1165) + 256*(mc 2010 + mc 1166 - mc 2353*mc 1166 - 2*mc 2010*mc 1166 + 2*mc 2010*mc 2353*mc 1166) + 512*(mc 2011 + mc 1167 - mc 2354*mc 1167 - 2*mc 2011*mc 1167 + 2*mc 2011*mc 2354*mc 1167) + 1024*(mc 2012 + mc 1168 - mc 2355*mc 1168 - 2*mc 2012*mc 1168 + 2*mc 2012*mc 2355*mc 1168) + 2048*(mc 2013 + mc 1169 - mc 2356*mc 1169 - 2*mc 2013*mc 1169 + 2*mc 2013*mc 2356*mc 1169) + 4096*(mc 2014 + mc 1170 - mc 2357*mc 1170 - 2*mc 2014*mc 1170 + 2*mc 2014*mc 2357*mc 1170) + 8192*(mc 2015 + mc 1171 - mc 2358*mc 1171 - 2*mc 2015*mc 1171 + 2*mc 2015*mc 2358*mc 1171) + 16384*(mc 2016 + mc 1172 - mc 2359*mc 1172 - 2*mc 2016*mc 1172 + 2*mc 2016*mc 2359*mc 1172) + 32768*(mc 1953 + mc 1173 - mc 2360*mc 1173 - 2*mc 1953*mc 1173 + 2*mc 1953*mc 2360*mc 1173)) - mc 2537 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2982, KeccakfPermAir.extraction.inter_6002, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6001 c row = (mc 2003 + mc 1159 - mc 2346*mc 1159 - 2*mc 2003*mc 1159 + 2*mc 2003*mc 2346*mc 1159) + 2 * KeccakfPermAir.extraction.inter_5999 c row := by
    simp only [KeccakfPermAir.extraction.inter_6001, KeccakfPermAir.extraction.inter_6000, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_5999 c row = (mc 2004 + mc 1160 - mc 2347*mc 1160 - 2*mc 2004*mc 1160 + 2*mc 2004*mc 2347*mc 1160) + 2 * KeccakfPermAir.extraction.inter_5997 c row := by
    simp only [KeccakfPermAir.extraction.inter_5999, KeccakfPermAir.extraction.inter_5998, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_5997 c row = (mc 2005 + mc 1161 - mc 2348*mc 1161 - 2*mc 2005*mc 1161 + 2*mc 2005*mc 2348*mc 1161) + 2 * KeccakfPermAir.extraction.inter_5995 c row := by
    simp only [KeccakfPermAir.extraction.inter_5997, KeccakfPermAir.extraction.inter_5996, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_5995 c row = (mc 2006 + mc 1162 - mc 2349*mc 1162 - 2*mc 2006*mc 1162 + 2*mc 2006*mc 2349*mc 1162) + 2 * KeccakfPermAir.extraction.inter_5993 c row := by
    simp only [KeccakfPermAir.extraction.inter_5995, KeccakfPermAir.extraction.inter_5994, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_5993 c row = (mc 2007 + mc 1163 - mc 2350*mc 1163 - 2*mc 2007*mc 1163 + 2*mc 2007*mc 2350*mc 1163) + 2 * KeccakfPermAir.extraction.inter_5991 c row := by
    simp only [KeccakfPermAir.extraction.inter_5993, KeccakfPermAir.extraction.inter_5992, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_5991 c row = (mc 2008 + mc 1164 - mc 2351*mc 1164 - 2*mc 2008*mc 1164 + 2*mc 2008*mc 2351*mc 1164) + 2 * KeccakfPermAir.extraction.inter_5989 c row := by
    simp only [KeccakfPermAir.extraction.inter_5991, KeccakfPermAir.extraction.inter_5990, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_5989 c row = (mc 2009 + mc 1165 - mc 2352*mc 1165 - 2*mc 2009*mc 1165 + 2*mc 2009*mc 2352*mc 1165) + 2 * KeccakfPermAir.extraction.inter_5987 c row := by
    simp only [KeccakfPermAir.extraction.inter_5989, KeccakfPermAir.extraction.inter_5988, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_5987 c row = (mc 2010 + mc 1166 - mc 2353*mc 1166 - 2*mc 2010*mc 1166 + 2*mc 2010*mc 2353*mc 1166) + 2 * KeccakfPermAir.extraction.inter_5985 c row := by
    simp only [KeccakfPermAir.extraction.inter_5987, KeccakfPermAir.extraction.inter_5986, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_5985 c row = (mc 2011 + mc 1167 - mc 2354*mc 1167 - 2*mc 2011*mc 1167 + 2*mc 2011*mc 2354*mc 1167) + 2 * KeccakfPermAir.extraction.inter_5983 c row := by
    simp only [KeccakfPermAir.extraction.inter_5985, KeccakfPermAir.extraction.inter_5984, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_5983 c row = (mc 2012 + mc 1168 - mc 2355*mc 1168 - 2*mc 2012*mc 1168 + 2*mc 2012*mc 2355*mc 1168) + 2 * KeccakfPermAir.extraction.inter_5981 c row := by
    simp only [KeccakfPermAir.extraction.inter_5983, KeccakfPermAir.extraction.inter_5982, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_5981 c row = (mc 2013 + mc 1169 - mc 2356*mc 1169 - 2*mc 2013*mc 1169 + 2*mc 2013*mc 2356*mc 1169) + 2 * KeccakfPermAir.extraction.inter_5979 c row := by
    simp only [KeccakfPermAir.extraction.inter_5981, KeccakfPermAir.extraction.inter_5980, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_5979 c row = (mc 2014 + mc 1170 - mc 2357*mc 1170 - 2*mc 2014*mc 1170 + 2*mc 2014*mc 2357*mc 1170) + 2 * KeccakfPermAir.extraction.inter_5977 c row := by
    simp only [KeccakfPermAir.extraction.inter_5979, KeccakfPermAir.extraction.inter_5978, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_5977 c row = (mc 2015 + mc 1171 - mc 2358*mc 1171 - 2*mc 2015*mc 1171 + 2*mc 2015*mc 2358*mc 1171) + 2 * KeccakfPermAir.extraction.inter_5975 c row := by
    simp only [KeccakfPermAir.extraction.inter_5977, KeccakfPermAir.extraction.inter_5976, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_5975 c row = (mc 2016 + mc 1172 - mc 2359*mc 1172 - 2*mc 2016*mc 1172 + 2*mc 2016*mc 2359*mc 1172) + 2 * KeccakfPermAir.extraction.inter_5973 c row := by
    simp only [KeccakfPermAir.extraction.inter_5975, KeccakfPermAir.extraction.inter_5974, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_5973 c row = (mc 1953 + mc 1173 - mc 2360*mc 1173 - 2*mc 1953*mc 1173 + 2*mc 1953*mc 2360*mc 1173) := by
    simp only [KeccakfPermAir.extraction.inter_5973, KeccakfPermAir.extraction.inter_5972, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2983 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2983 c row) :
    ((mc 1954 + mc 1174 - mc 2361*mc 1174 - 2*mc 1954*mc 1174 + 2*mc 1954*mc 2361*mc 1174) + 2*(mc 1955 + mc 1175 - mc 2362*mc 1175 - 2*mc 1955*mc 1175 + 2*mc 1955*mc 2362*mc 1175) + 4*(mc 1956 + mc 1176 - mc 2363*mc 1176 - 2*mc 1956*mc 1176 + 2*mc 1956*mc 2363*mc 1176) + 8*(mc 1957 + mc 1177 - mc 2364*mc 1177 - 2*mc 1957*mc 1177 + 2*mc 1957*mc 2364*mc 1177) + 16*(mc 1958 + mc 1178 - mc 2365*mc 1178 - 2*mc 1958*mc 1178 + 2*mc 1958*mc 2365*mc 1178) + 32*(mc 1959 + mc 1179 - mc 2366*mc 1179 - 2*mc 1959*mc 1179 + 2*mc 1959*mc 2366*mc 1179) + 64*(mc 1960 + mc 1180 - mc 2367*mc 1180 - 2*mc 1960*mc 1180 + 2*mc 1960*mc 2367*mc 1180) + 128*(mc 1961 + mc 1181 - mc 2368*mc 1181 - 2*mc 1961*mc 1181 + 2*mc 1961*mc 2368*mc 1181) + 256*(mc 1962 + mc 1182 - mc 2369*mc 1182 - 2*mc 1962*mc 1182 + 2*mc 1962*mc 2369*mc 1182) + 512*(mc 1963 + mc 1183 - mc 2370*mc 1183 - 2*mc 1963*mc 1183 + 2*mc 1963*mc 2370*mc 1183) + 1024*(mc 1964 + mc 1184 - mc 2371*mc 1184 - 2*mc 1964*mc 1184 + 2*mc 1964*mc 2371*mc 1184) + 2048*(mc 1965 + mc 1121 - mc 2372*mc 1121 - 2*mc 1965*mc 1121 + 2*mc 1965*mc 2372*mc 1121) + 4096*(mc 1966 + mc 1122 - mc 2373*mc 1122 - 2*mc 1966*mc 1122 + 2*mc 1966*mc 2373*mc 1122) + 8192*(mc 1967 + mc 1123 - mc 2374*mc 1123 - 2*mc 1967*mc 1123 + 2*mc 1967*mc 2374*mc 1123) + 16384*(mc 1968 + mc 1124 - mc 2375*mc 1124 - 2*mc 1968*mc 1124 + 2*mc 1968*mc 2375*mc 1124) + 32768*(mc 1969 + mc 1125 - mc 2376*mc 1125 - 2*mc 1969*mc 1125 + 2*mc 1969*mc 2376*mc 1125)) - mc 2538 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2983, KeccakfPermAir.extraction.inter_6033, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6032 c row = (mc 1955 + mc 1175 - mc 2362*mc 1175 - 2*mc 1955*mc 1175 + 2*mc 1955*mc 2362*mc 1175) + 2 * KeccakfPermAir.extraction.inter_6030 c row := by
    simp only [KeccakfPermAir.extraction.inter_6032, KeccakfPermAir.extraction.inter_6031, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6030 c row = (mc 1956 + mc 1176 - mc 2363*mc 1176 - 2*mc 1956*mc 1176 + 2*mc 1956*mc 2363*mc 1176) + 2 * KeccakfPermAir.extraction.inter_6028 c row := by
    simp only [KeccakfPermAir.extraction.inter_6030, KeccakfPermAir.extraction.inter_6029, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6028 c row = (mc 1957 + mc 1177 - mc 2364*mc 1177 - 2*mc 1957*mc 1177 + 2*mc 1957*mc 2364*mc 1177) + 2 * KeccakfPermAir.extraction.inter_6026 c row := by
    simp only [KeccakfPermAir.extraction.inter_6028, KeccakfPermAir.extraction.inter_6027, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6026 c row = (mc 1958 + mc 1178 - mc 2365*mc 1178 - 2*mc 1958*mc 1178 + 2*mc 1958*mc 2365*mc 1178) + 2 * KeccakfPermAir.extraction.inter_6024 c row := by
    simp only [KeccakfPermAir.extraction.inter_6026, KeccakfPermAir.extraction.inter_6025, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6024 c row = (mc 1959 + mc 1179 - mc 2366*mc 1179 - 2*mc 1959*mc 1179 + 2*mc 1959*mc 2366*mc 1179) + 2 * KeccakfPermAir.extraction.inter_6022 c row := by
    simp only [KeccakfPermAir.extraction.inter_6024, KeccakfPermAir.extraction.inter_6023, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6022 c row = (mc 1960 + mc 1180 - mc 2367*mc 1180 - 2*mc 1960*mc 1180 + 2*mc 1960*mc 2367*mc 1180) + 2 * KeccakfPermAir.extraction.inter_6020 c row := by
    simp only [KeccakfPermAir.extraction.inter_6022, KeccakfPermAir.extraction.inter_6021, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6020 c row = (mc 1961 + mc 1181 - mc 2368*mc 1181 - 2*mc 1961*mc 1181 + 2*mc 1961*mc 2368*mc 1181) + 2 * KeccakfPermAir.extraction.inter_6018 c row := by
    simp only [KeccakfPermAir.extraction.inter_6020, KeccakfPermAir.extraction.inter_6019, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6018 c row = (mc 1962 + mc 1182 - mc 2369*mc 1182 - 2*mc 1962*mc 1182 + 2*mc 1962*mc 2369*mc 1182) + 2 * KeccakfPermAir.extraction.inter_6016 c row := by
    simp only [KeccakfPermAir.extraction.inter_6018, KeccakfPermAir.extraction.inter_6017, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6016 c row = (mc 1963 + mc 1183 - mc 2370*mc 1183 - 2*mc 1963*mc 1183 + 2*mc 1963*mc 2370*mc 1183) + 2 * KeccakfPermAir.extraction.inter_6014 c row := by
    simp only [KeccakfPermAir.extraction.inter_6016, KeccakfPermAir.extraction.inter_6015, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6014 c row = (mc 1964 + mc 1184 - mc 2371*mc 1184 - 2*mc 1964*mc 1184 + 2*mc 1964*mc 2371*mc 1184) + 2 * KeccakfPermAir.extraction.inter_6012 c row := by
    simp only [KeccakfPermAir.extraction.inter_6014, KeccakfPermAir.extraction.inter_6013, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6012 c row = (mc 1965 + mc 1121 - mc 2372*mc 1121 - 2*mc 1965*mc 1121 + 2*mc 1965*mc 2372*mc 1121) + 2 * KeccakfPermAir.extraction.inter_6010 c row := by
    simp only [KeccakfPermAir.extraction.inter_6012, KeccakfPermAir.extraction.inter_6011, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6010 c row = (mc 1966 + mc 1122 - mc 2373*mc 1122 - 2*mc 1966*mc 1122 + 2*mc 1966*mc 2373*mc 1122) + 2 * KeccakfPermAir.extraction.inter_6008 c row := by
    simp only [KeccakfPermAir.extraction.inter_6010, KeccakfPermAir.extraction.inter_6009, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6008 c row = (mc 1967 + mc 1123 - mc 2374*mc 1123 - 2*mc 1967*mc 1123 + 2*mc 1967*mc 2374*mc 1123) + 2 * KeccakfPermAir.extraction.inter_6006 c row := by
    simp only [KeccakfPermAir.extraction.inter_6008, KeccakfPermAir.extraction.inter_6007, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6006 c row = (mc 1968 + mc 1124 - mc 2375*mc 1124 - 2*mc 1968*mc 1124 + 2*mc 1968*mc 2375*mc 1124) + 2 * KeccakfPermAir.extraction.inter_6004 c row := by
    simp only [KeccakfPermAir.extraction.inter_6006, KeccakfPermAir.extraction.inter_6005, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6004 c row = (mc 1969 + mc 1125 - mc 2376*mc 1125 - 2*mc 1969*mc 1125 + 2*mc 1969*mc 2376*mc 1125) := by
    simp only [KeccakfPermAir.extraction.inter_6004, KeccakfPermAir.extraction.inter_6003, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2984 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2984 c row) :
    ((mc 1970 + mc 1126 - mc 2377*mc 1126 - 2*mc 1970*mc 1126 + 2*mc 1970*mc 2377*mc 1126) + 2*(mc 1971 + mc 1127 - mc 2378*mc 1127 - 2*mc 1971*mc 1127 + 2*mc 1971*mc 2378*mc 1127) + 4*(mc 1972 + mc 1128 - mc 2379*mc 1128 - 2*mc 1972*mc 1128 + 2*mc 1972*mc 2379*mc 1128) + 8*(mc 1973 + mc 1129 - mc 2380*mc 1129 - 2*mc 1973*mc 1129 + 2*mc 1973*mc 2380*mc 1129) + 16*(mc 1974 + mc 1130 - mc 2381*mc 1130 - 2*mc 1974*mc 1130 + 2*mc 1974*mc 2381*mc 1130) + 32*(mc 1975 + mc 1131 - mc 2382*mc 1131 - 2*mc 1975*mc 1131 + 2*mc 1975*mc 2382*mc 1131) + 64*(mc 1976 + mc 1132 - mc 2383*mc 1132 - 2*mc 1976*mc 1132 + 2*mc 1976*mc 2383*mc 1132) + 128*(mc 1977 + mc 1133 - mc 2384*mc 1133 - 2*mc 1977*mc 1133 + 2*mc 1977*mc 2384*mc 1133) + 256*(mc 1978 + mc 1134 - mc 2385*mc 1134 - 2*mc 1978*mc 1134 + 2*mc 1978*mc 2385*mc 1134) + 512*(mc 1979 + mc 1135 - mc 2386*mc 1135 - 2*mc 1979*mc 1135 + 2*mc 1979*mc 2386*mc 1135) + 1024*(mc 1980 + mc 1136 - mc 2387*mc 1136 - 2*mc 1980*mc 1136 + 2*mc 1980*mc 2387*mc 1136) + 2048*(mc 1981 + mc 1137 - mc 2388*mc 1137 - 2*mc 1981*mc 1137 + 2*mc 1981*mc 2388*mc 1137) + 4096*(mc 1982 + mc 1138 - mc 2389*mc 1138 - 2*mc 1982*mc 1138 + 2*mc 1982*mc 2389*mc 1138) + 8192*(mc 1983 + mc 1139 - mc 2390*mc 1139 - 2*mc 1983*mc 1139 + 2*mc 1983*mc 2390*mc 1139) + 16384*(mc 1984 + mc 1140 - mc 2391*mc 1140 - 2*mc 1984*mc 1140 + 2*mc 1984*mc 2391*mc 1140) + 32768*(mc 1985 + mc 1141 - mc 2392*mc 1141 - 2*mc 1985*mc 1141 + 2*mc 1985*mc 2392*mc 1141)) - mc 2539 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2984, KeccakfPermAir.extraction.inter_6064, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6063 c row = (mc 1971 + mc 1127 - mc 2378*mc 1127 - 2*mc 1971*mc 1127 + 2*mc 1971*mc 2378*mc 1127) + 2 * KeccakfPermAir.extraction.inter_6061 c row := by
    simp only [KeccakfPermAir.extraction.inter_6063, KeccakfPermAir.extraction.inter_6062, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6061 c row = (mc 1972 + mc 1128 - mc 2379*mc 1128 - 2*mc 1972*mc 1128 + 2*mc 1972*mc 2379*mc 1128) + 2 * KeccakfPermAir.extraction.inter_6059 c row := by
    simp only [KeccakfPermAir.extraction.inter_6061, KeccakfPermAir.extraction.inter_6060, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6059 c row = (mc 1973 + mc 1129 - mc 2380*mc 1129 - 2*mc 1973*mc 1129 + 2*mc 1973*mc 2380*mc 1129) + 2 * KeccakfPermAir.extraction.inter_6057 c row := by
    simp only [KeccakfPermAir.extraction.inter_6059, KeccakfPermAir.extraction.inter_6058, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6057 c row = (mc 1974 + mc 1130 - mc 2381*mc 1130 - 2*mc 1974*mc 1130 + 2*mc 1974*mc 2381*mc 1130) + 2 * KeccakfPermAir.extraction.inter_6055 c row := by
    simp only [KeccakfPermAir.extraction.inter_6057, KeccakfPermAir.extraction.inter_6056, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6055 c row = (mc 1975 + mc 1131 - mc 2382*mc 1131 - 2*mc 1975*mc 1131 + 2*mc 1975*mc 2382*mc 1131) + 2 * KeccakfPermAir.extraction.inter_6053 c row := by
    simp only [KeccakfPermAir.extraction.inter_6055, KeccakfPermAir.extraction.inter_6054, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6053 c row = (mc 1976 + mc 1132 - mc 2383*mc 1132 - 2*mc 1976*mc 1132 + 2*mc 1976*mc 2383*mc 1132) + 2 * KeccakfPermAir.extraction.inter_6051 c row := by
    simp only [KeccakfPermAir.extraction.inter_6053, KeccakfPermAir.extraction.inter_6052, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6051 c row = (mc 1977 + mc 1133 - mc 2384*mc 1133 - 2*mc 1977*mc 1133 + 2*mc 1977*mc 2384*mc 1133) + 2 * KeccakfPermAir.extraction.inter_6049 c row := by
    simp only [KeccakfPermAir.extraction.inter_6051, KeccakfPermAir.extraction.inter_6050, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6049 c row = (mc 1978 + mc 1134 - mc 2385*mc 1134 - 2*mc 1978*mc 1134 + 2*mc 1978*mc 2385*mc 1134) + 2 * KeccakfPermAir.extraction.inter_6047 c row := by
    simp only [KeccakfPermAir.extraction.inter_6049, KeccakfPermAir.extraction.inter_6048, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6047 c row = (mc 1979 + mc 1135 - mc 2386*mc 1135 - 2*mc 1979*mc 1135 + 2*mc 1979*mc 2386*mc 1135) + 2 * KeccakfPermAir.extraction.inter_6045 c row := by
    simp only [KeccakfPermAir.extraction.inter_6047, KeccakfPermAir.extraction.inter_6046, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6045 c row = (mc 1980 + mc 1136 - mc 2387*mc 1136 - 2*mc 1980*mc 1136 + 2*mc 1980*mc 2387*mc 1136) + 2 * KeccakfPermAir.extraction.inter_6043 c row := by
    simp only [KeccakfPermAir.extraction.inter_6045, KeccakfPermAir.extraction.inter_6044, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6043 c row = (mc 1981 + mc 1137 - mc 2388*mc 1137 - 2*mc 1981*mc 1137 + 2*mc 1981*mc 2388*mc 1137) + 2 * KeccakfPermAir.extraction.inter_6041 c row := by
    simp only [KeccakfPermAir.extraction.inter_6043, KeccakfPermAir.extraction.inter_6042, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6041 c row = (mc 1982 + mc 1138 - mc 2389*mc 1138 - 2*mc 1982*mc 1138 + 2*mc 1982*mc 2389*mc 1138) + 2 * KeccakfPermAir.extraction.inter_6039 c row := by
    simp only [KeccakfPermAir.extraction.inter_6041, KeccakfPermAir.extraction.inter_6040, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6039 c row = (mc 1983 + mc 1139 - mc 2390*mc 1139 - 2*mc 1983*mc 1139 + 2*mc 1983*mc 2390*mc 1139) + 2 * KeccakfPermAir.extraction.inter_6037 c row := by
    simp only [KeccakfPermAir.extraction.inter_6039, KeccakfPermAir.extraction.inter_6038, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6037 c row = (mc 1984 + mc 1140 - mc 2391*mc 1140 - 2*mc 1984*mc 1140 + 2*mc 1984*mc 2391*mc 1140) + 2 * KeccakfPermAir.extraction.inter_6035 c row := by
    simp only [KeccakfPermAir.extraction.inter_6037, KeccakfPermAir.extraction.inter_6036, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6035 c row = (mc 1985 + mc 1141 - mc 2392*mc 1141 - 2*mc 1985*mc 1141 + 2*mc 1985*mc 2392*mc 1141) := by
    simp only [KeccakfPermAir.extraction.inter_6035, KeccakfPermAir.extraction.inter_6034, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2985 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2985 c row) :
    ((mc 1986 + mc 1142 - mc 2393*mc 1142 - 2*mc 1986*mc 1142 + 2*mc 1986*mc 2393*mc 1142) + 2*(mc 1987 + mc 1143 - mc 2394*mc 1143 - 2*mc 1987*mc 1143 + 2*mc 1987*mc 2394*mc 1143) + 4*(mc 1988 + mc 1144 - mc 2395*mc 1144 - 2*mc 1988*mc 1144 + 2*mc 1988*mc 2395*mc 1144) + 8*(mc 1989 + mc 1145 - mc 2396*mc 1145 - 2*mc 1989*mc 1145 + 2*mc 1989*mc 2396*mc 1145) + 16*(mc 1990 + mc 1146 - mc 2397*mc 1146 - 2*mc 1990*mc 1146 + 2*mc 1990*mc 2397*mc 1146) + 32*(mc 1991 + mc 1147 - mc 2398*mc 1147 - 2*mc 1991*mc 1147 + 2*mc 1991*mc 2398*mc 1147) + 64*(mc 1992 + mc 1148 - mc 2399*mc 1148 - 2*mc 1992*mc 1148 + 2*mc 1992*mc 2399*mc 1148) + 128*(mc 1993 + mc 1149 - mc 2400*mc 1149 - 2*mc 1993*mc 1149 + 2*mc 1993*mc 2400*mc 1149) + 256*(mc 1994 + mc 1150 - mc 2337*mc 1150 - 2*mc 1994*mc 1150 + 2*mc 1994*mc 2337*mc 1150) + 512*(mc 1995 + mc 1151 - mc 2338*mc 1151 - 2*mc 1995*mc 1151 + 2*mc 1995*mc 2338*mc 1151) + 1024*(mc 1996 + mc 1152 - mc 2339*mc 1152 - 2*mc 1996*mc 1152 + 2*mc 1996*mc 2339*mc 1152) + 2048*(mc 1997 + mc 1153 - mc 2340*mc 1153 - 2*mc 1997*mc 1153 + 2*mc 1997*mc 2340*mc 1153) + 4096*(mc 1998 + mc 1154 - mc 2341*mc 1154 - 2*mc 1998*mc 1154 + 2*mc 1998*mc 2341*mc 1154) + 8192*(mc 1999 + mc 1155 - mc 2342*mc 1155 - 2*mc 1999*mc 1155 + 2*mc 1999*mc 2342*mc 1155) + 16384*(mc 2000 + mc 1156 - mc 2343*mc 1156 - 2*mc 2000*mc 1156 + 2*mc 2000*mc 2343*mc 1156) + 32768*(mc 2001 + mc 1157 - mc 2344*mc 1157 - 2*mc 2001*mc 1157 + 2*mc 2001*mc 2344*mc 1157)) - mc 2540 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2985, KeccakfPermAir.extraction.inter_6095, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6094 c row = (mc 1987 + mc 1143 - mc 2394*mc 1143 - 2*mc 1987*mc 1143 + 2*mc 1987*mc 2394*mc 1143) + 2 * KeccakfPermAir.extraction.inter_6092 c row := by
    simp only [KeccakfPermAir.extraction.inter_6094, KeccakfPermAir.extraction.inter_6093, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6092 c row = (mc 1988 + mc 1144 - mc 2395*mc 1144 - 2*mc 1988*mc 1144 + 2*mc 1988*mc 2395*mc 1144) + 2 * KeccakfPermAir.extraction.inter_6090 c row := by
    simp only [KeccakfPermAir.extraction.inter_6092, KeccakfPermAir.extraction.inter_6091, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6090 c row = (mc 1989 + mc 1145 - mc 2396*mc 1145 - 2*mc 1989*mc 1145 + 2*mc 1989*mc 2396*mc 1145) + 2 * KeccakfPermAir.extraction.inter_6088 c row := by
    simp only [KeccakfPermAir.extraction.inter_6090, KeccakfPermAir.extraction.inter_6089, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6088 c row = (mc 1990 + mc 1146 - mc 2397*mc 1146 - 2*mc 1990*mc 1146 + 2*mc 1990*mc 2397*mc 1146) + 2 * KeccakfPermAir.extraction.inter_6086 c row := by
    simp only [KeccakfPermAir.extraction.inter_6088, KeccakfPermAir.extraction.inter_6087, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6086 c row = (mc 1991 + mc 1147 - mc 2398*mc 1147 - 2*mc 1991*mc 1147 + 2*mc 1991*mc 2398*mc 1147) + 2 * KeccakfPermAir.extraction.inter_6084 c row := by
    simp only [KeccakfPermAir.extraction.inter_6086, KeccakfPermAir.extraction.inter_6085, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6084 c row = (mc 1992 + mc 1148 - mc 2399*mc 1148 - 2*mc 1992*mc 1148 + 2*mc 1992*mc 2399*mc 1148) + 2 * KeccakfPermAir.extraction.inter_6082 c row := by
    simp only [KeccakfPermAir.extraction.inter_6084, KeccakfPermAir.extraction.inter_6083, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6082 c row = (mc 1993 + mc 1149 - mc 2400*mc 1149 - 2*mc 1993*mc 1149 + 2*mc 1993*mc 2400*mc 1149) + 2 * KeccakfPermAir.extraction.inter_6080 c row := by
    simp only [KeccakfPermAir.extraction.inter_6082, KeccakfPermAir.extraction.inter_6081, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6080 c row = (mc 1994 + mc 1150 - mc 2337*mc 1150 - 2*mc 1994*mc 1150 + 2*mc 1994*mc 2337*mc 1150) + 2 * KeccakfPermAir.extraction.inter_6078 c row := by
    simp only [KeccakfPermAir.extraction.inter_6080, KeccakfPermAir.extraction.inter_6079, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6078 c row = (mc 1995 + mc 1151 - mc 2338*mc 1151 - 2*mc 1995*mc 1151 + 2*mc 1995*mc 2338*mc 1151) + 2 * KeccakfPermAir.extraction.inter_6076 c row := by
    simp only [KeccakfPermAir.extraction.inter_6078, KeccakfPermAir.extraction.inter_6077, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6076 c row = (mc 1996 + mc 1152 - mc 2339*mc 1152 - 2*mc 1996*mc 1152 + 2*mc 1996*mc 2339*mc 1152) + 2 * KeccakfPermAir.extraction.inter_6074 c row := by
    simp only [KeccakfPermAir.extraction.inter_6076, KeccakfPermAir.extraction.inter_6075, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6074 c row = (mc 1997 + mc 1153 - mc 2340*mc 1153 - 2*mc 1997*mc 1153 + 2*mc 1997*mc 2340*mc 1153) + 2 * KeccakfPermAir.extraction.inter_6072 c row := by
    simp only [KeccakfPermAir.extraction.inter_6074, KeccakfPermAir.extraction.inter_6073, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6072 c row = (mc 1998 + mc 1154 - mc 2341*mc 1154 - 2*mc 1998*mc 1154 + 2*mc 1998*mc 2341*mc 1154) + 2 * KeccakfPermAir.extraction.inter_6070 c row := by
    simp only [KeccakfPermAir.extraction.inter_6072, KeccakfPermAir.extraction.inter_6071, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6070 c row = (mc 1999 + mc 1155 - mc 2342*mc 1155 - 2*mc 1999*mc 1155 + 2*mc 1999*mc 2342*mc 1155) + 2 * KeccakfPermAir.extraction.inter_6068 c row := by
    simp only [KeccakfPermAir.extraction.inter_6070, KeccakfPermAir.extraction.inter_6069, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6068 c row = (mc 2000 + mc 1156 - mc 2343*mc 1156 - 2*mc 2000*mc 1156 + 2*mc 2000*mc 2343*mc 1156) + 2 * KeccakfPermAir.extraction.inter_6066 c row := by
    simp only [KeccakfPermAir.extraction.inter_6068, KeccakfPermAir.extraction.inter_6067, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6066 c row = (mc 2001 + mc 1157 - mc 2344*mc 1157 - 2*mc 2001*mc 1157 + 2*mc 2001*mc 2344*mc 1157) := by
    simp only [KeccakfPermAir.extraction.inter_6066, KeccakfPermAir.extraction.inter_6065, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2986 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2986 c row) :
    ((mc 2345 + mc 1213 - mc 1158*mc 1213 - 2*mc 2345*mc 1213 + 2*mc 2345*mc 1158*mc 1213) + 2*(mc 2346 + mc 1214 - mc 1159*mc 1214 - 2*mc 2346*mc 1214 + 2*mc 2346*mc 1159*mc 1214) + 4*(mc 2347 + mc 1215 - mc 1160*mc 1215 - 2*mc 2347*mc 1215 + 2*mc 2347*mc 1160*mc 1215) + 8*(mc 2348 + mc 1216 - mc 1161*mc 1216 - 2*mc 2348*mc 1216 + 2*mc 2348*mc 1161*mc 1216) + 16*(mc 2349 + mc 1217 - mc 1162*mc 1217 - 2*mc 2349*mc 1217 + 2*mc 2349*mc 1162*mc 1217) + 32*(mc 2350 + mc 1218 - mc 1163*mc 1218 - 2*mc 2350*mc 1218 + 2*mc 2350*mc 1163*mc 1218) + 64*(mc 2351 + mc 1219 - mc 1164*mc 1219 - 2*mc 2351*mc 1219 + 2*mc 2351*mc 1164*mc 1219) + 128*(mc 2352 + mc 1220 - mc 1165*mc 1220 - 2*mc 2352*mc 1220 + 2*mc 2352*mc 1165*mc 1220) + 256*(mc 2353 + mc 1221 - mc 1166*mc 1221 - 2*mc 2353*mc 1221 + 2*mc 2353*mc 1166*mc 1221) + 512*(mc 2354 + mc 1222 - mc 1167*mc 1222 - 2*mc 2354*mc 1222 + 2*mc 2354*mc 1167*mc 1222) + 1024*(mc 2355 + mc 1223 - mc 1168*mc 1223 - 2*mc 2355*mc 1223 + 2*mc 2355*mc 1168*mc 1223) + 2048*(mc 2356 + mc 1224 - mc 1169*mc 1224 - 2*mc 2356*mc 1224 + 2*mc 2356*mc 1169*mc 1224) + 4096*(mc 2357 + mc 1225 - mc 1170*mc 1225 - 2*mc 2357*mc 1225 + 2*mc 2357*mc 1170*mc 1225) + 8192*(mc 2358 + mc 1226 - mc 1171*mc 1226 - 2*mc 2358*mc 1226 + 2*mc 2358*mc 1171*mc 1226) + 16384*(mc 2359 + mc 1227 - mc 1172*mc 1227 - 2*mc 2359*mc 1227 + 2*mc 2359*mc 1172*mc 1227) + 32768*(mc 2360 + mc 1228 - mc 1173*mc 1228 - 2*mc 2360*mc 1228 + 2*mc 2360*mc 1173*mc 1228)) - mc 2541 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2986, KeccakfPermAir.extraction.inter_6126, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6125 c row = (mc 2346 + mc 1214 - mc 1159*mc 1214 - 2*mc 2346*mc 1214 + 2*mc 2346*mc 1159*mc 1214) + 2 * KeccakfPermAir.extraction.inter_6123 c row := by
    simp only [KeccakfPermAir.extraction.inter_6125, KeccakfPermAir.extraction.inter_6124, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6123 c row = (mc 2347 + mc 1215 - mc 1160*mc 1215 - 2*mc 2347*mc 1215 + 2*mc 2347*mc 1160*mc 1215) + 2 * KeccakfPermAir.extraction.inter_6121 c row := by
    simp only [KeccakfPermAir.extraction.inter_6123, KeccakfPermAir.extraction.inter_6122, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6121 c row = (mc 2348 + mc 1216 - mc 1161*mc 1216 - 2*mc 2348*mc 1216 + 2*mc 2348*mc 1161*mc 1216) + 2 * KeccakfPermAir.extraction.inter_6119 c row := by
    simp only [KeccakfPermAir.extraction.inter_6121, KeccakfPermAir.extraction.inter_6120, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6119 c row = (mc 2349 + mc 1217 - mc 1162*mc 1217 - 2*mc 2349*mc 1217 + 2*mc 2349*mc 1162*mc 1217) + 2 * KeccakfPermAir.extraction.inter_6117 c row := by
    simp only [KeccakfPermAir.extraction.inter_6119, KeccakfPermAir.extraction.inter_6118, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6117 c row = (mc 2350 + mc 1218 - mc 1163*mc 1218 - 2*mc 2350*mc 1218 + 2*mc 2350*mc 1163*mc 1218) + 2 * KeccakfPermAir.extraction.inter_6115 c row := by
    simp only [KeccakfPermAir.extraction.inter_6117, KeccakfPermAir.extraction.inter_6116, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6115 c row = (mc 2351 + mc 1219 - mc 1164*mc 1219 - 2*mc 2351*mc 1219 + 2*mc 2351*mc 1164*mc 1219) + 2 * KeccakfPermAir.extraction.inter_6113 c row := by
    simp only [KeccakfPermAir.extraction.inter_6115, KeccakfPermAir.extraction.inter_6114, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6113 c row = (mc 2352 + mc 1220 - mc 1165*mc 1220 - 2*mc 2352*mc 1220 + 2*mc 2352*mc 1165*mc 1220) + 2 * KeccakfPermAir.extraction.inter_6111 c row := by
    simp only [KeccakfPermAir.extraction.inter_6113, KeccakfPermAir.extraction.inter_6112, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6111 c row = (mc 2353 + mc 1221 - mc 1166*mc 1221 - 2*mc 2353*mc 1221 + 2*mc 2353*mc 1166*mc 1221) + 2 * KeccakfPermAir.extraction.inter_6109 c row := by
    simp only [KeccakfPermAir.extraction.inter_6111, KeccakfPermAir.extraction.inter_6110, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6109 c row = (mc 2354 + mc 1222 - mc 1167*mc 1222 - 2*mc 2354*mc 1222 + 2*mc 2354*mc 1167*mc 1222) + 2 * KeccakfPermAir.extraction.inter_6107 c row := by
    simp only [KeccakfPermAir.extraction.inter_6109, KeccakfPermAir.extraction.inter_6108, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6107 c row = (mc 2355 + mc 1223 - mc 1168*mc 1223 - 2*mc 2355*mc 1223 + 2*mc 2355*mc 1168*mc 1223) + 2 * KeccakfPermAir.extraction.inter_6105 c row := by
    simp only [KeccakfPermAir.extraction.inter_6107, KeccakfPermAir.extraction.inter_6106, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6105 c row = (mc 2356 + mc 1224 - mc 1169*mc 1224 - 2*mc 2356*mc 1224 + 2*mc 2356*mc 1169*mc 1224) + 2 * KeccakfPermAir.extraction.inter_6103 c row := by
    simp only [KeccakfPermAir.extraction.inter_6105, KeccakfPermAir.extraction.inter_6104, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6103 c row = (mc 2357 + mc 1225 - mc 1170*mc 1225 - 2*mc 2357*mc 1225 + 2*mc 2357*mc 1170*mc 1225) + 2 * KeccakfPermAir.extraction.inter_6101 c row := by
    simp only [KeccakfPermAir.extraction.inter_6103, KeccakfPermAir.extraction.inter_6102, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6101 c row = (mc 2358 + mc 1226 - mc 1171*mc 1226 - 2*mc 2358*mc 1226 + 2*mc 2358*mc 1171*mc 1226) + 2 * KeccakfPermAir.extraction.inter_6099 c row := by
    simp only [KeccakfPermAir.extraction.inter_6101, KeccakfPermAir.extraction.inter_6100, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6099 c row = (mc 2359 + mc 1227 - mc 1172*mc 1227 - 2*mc 2359*mc 1227 + 2*mc 2359*mc 1172*mc 1227) + 2 * KeccakfPermAir.extraction.inter_6097 c row := by
    simp only [KeccakfPermAir.extraction.inter_6099, KeccakfPermAir.extraction.inter_6098, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6097 c row = (mc 2360 + mc 1228 - mc 1173*mc 1228 - 2*mc 2360*mc 1228 + 2*mc 2360*mc 1173*mc 1228) := by
    simp only [KeccakfPermAir.extraction.inter_6097, KeccakfPermAir.extraction.inter_6096, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2987 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2987 c row) :
    ((mc 2361 + mc 1229 - mc 1174*mc 1229 - 2*mc 2361*mc 1229 + 2*mc 2361*mc 1174*mc 1229) + 2*(mc 2362 + mc 1230 - mc 1175*mc 1230 - 2*mc 2362*mc 1230 + 2*mc 2362*mc 1175*mc 1230) + 4*(mc 2363 + mc 1231 - mc 1176*mc 1231 - 2*mc 2363*mc 1231 + 2*mc 2363*mc 1176*mc 1231) + 8*(mc 2364 + mc 1232 - mc 1177*mc 1232 - 2*mc 2364*mc 1232 + 2*mc 2364*mc 1177*mc 1232) + 16*(mc 2365 + mc 1233 - mc 1178*mc 1233 - 2*mc 2365*mc 1233 + 2*mc 2365*mc 1178*mc 1233) + 32*(mc 2366 + mc 1234 - mc 1179*mc 1234 - 2*mc 2366*mc 1234 + 2*mc 2366*mc 1179*mc 1234) + 64*(mc 2367 + mc 1235 - mc 1180*mc 1235 - 2*mc 2367*mc 1235 + 2*mc 2367*mc 1180*mc 1235) + 128*(mc 2368 + mc 1236 - mc 1181*mc 1236 - 2*mc 2368*mc 1236 + 2*mc 2368*mc 1181*mc 1236) + 256*(mc 2369 + mc 1237 - mc 1182*mc 1237 - 2*mc 2369*mc 1237 + 2*mc 2369*mc 1182*mc 1237) + 512*(mc 2370 + mc 1238 - mc 1183*mc 1238 - 2*mc 2370*mc 1238 + 2*mc 2370*mc 1183*mc 1238) + 1024*(mc 2371 + mc 1239 - mc 1184*mc 1239 - 2*mc 2371*mc 1239 + 2*mc 2371*mc 1184*mc 1239) + 2048*(mc 2372 + mc 1240 - mc 1121*mc 1240 - 2*mc 2372*mc 1240 + 2*mc 2372*mc 1121*mc 1240) + 4096*(mc 2373 + mc 1241 - mc 1122*mc 1241 - 2*mc 2373*mc 1241 + 2*mc 2373*mc 1122*mc 1241) + 8192*(mc 2374 + mc 1242 - mc 1123*mc 1242 - 2*mc 2374*mc 1242 + 2*mc 2374*mc 1123*mc 1242) + 16384*(mc 2375 + mc 1243 - mc 1124*mc 1243 - 2*mc 2375*mc 1243 + 2*mc 2375*mc 1124*mc 1243) + 32768*(mc 2376 + mc 1244 - mc 1125*mc 1244 - 2*mc 2376*mc 1244 + 2*mc 2376*mc 1125*mc 1244)) - mc 2542 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2987, KeccakfPermAir.extraction.inter_6157, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6156 c row = (mc 2362 + mc 1230 - mc 1175*mc 1230 - 2*mc 2362*mc 1230 + 2*mc 2362*mc 1175*mc 1230) + 2 * KeccakfPermAir.extraction.inter_6154 c row := by
    simp only [KeccakfPermAir.extraction.inter_6156, KeccakfPermAir.extraction.inter_6155, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6154 c row = (mc 2363 + mc 1231 - mc 1176*mc 1231 - 2*mc 2363*mc 1231 + 2*mc 2363*mc 1176*mc 1231) + 2 * KeccakfPermAir.extraction.inter_6152 c row := by
    simp only [KeccakfPermAir.extraction.inter_6154, KeccakfPermAir.extraction.inter_6153, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6152 c row = (mc 2364 + mc 1232 - mc 1177*mc 1232 - 2*mc 2364*mc 1232 + 2*mc 2364*mc 1177*mc 1232) + 2 * KeccakfPermAir.extraction.inter_6150 c row := by
    simp only [KeccakfPermAir.extraction.inter_6152, KeccakfPermAir.extraction.inter_6151, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6150 c row = (mc 2365 + mc 1233 - mc 1178*mc 1233 - 2*mc 2365*mc 1233 + 2*mc 2365*mc 1178*mc 1233) + 2 * KeccakfPermAir.extraction.inter_6148 c row := by
    simp only [KeccakfPermAir.extraction.inter_6150, KeccakfPermAir.extraction.inter_6149, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6148 c row = (mc 2366 + mc 1234 - mc 1179*mc 1234 - 2*mc 2366*mc 1234 + 2*mc 2366*mc 1179*mc 1234) + 2 * KeccakfPermAir.extraction.inter_6146 c row := by
    simp only [KeccakfPermAir.extraction.inter_6148, KeccakfPermAir.extraction.inter_6147, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6146 c row = (mc 2367 + mc 1235 - mc 1180*mc 1235 - 2*mc 2367*mc 1235 + 2*mc 2367*mc 1180*mc 1235) + 2 * KeccakfPermAir.extraction.inter_6144 c row := by
    simp only [KeccakfPermAir.extraction.inter_6146, KeccakfPermAir.extraction.inter_6145, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6144 c row = (mc 2368 + mc 1236 - mc 1181*mc 1236 - 2*mc 2368*mc 1236 + 2*mc 2368*mc 1181*mc 1236) + 2 * KeccakfPermAir.extraction.inter_6142 c row := by
    simp only [KeccakfPermAir.extraction.inter_6144, KeccakfPermAir.extraction.inter_6143, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6142 c row = (mc 2369 + mc 1237 - mc 1182*mc 1237 - 2*mc 2369*mc 1237 + 2*mc 2369*mc 1182*mc 1237) + 2 * KeccakfPermAir.extraction.inter_6140 c row := by
    simp only [KeccakfPermAir.extraction.inter_6142, KeccakfPermAir.extraction.inter_6141, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6140 c row = (mc 2370 + mc 1238 - mc 1183*mc 1238 - 2*mc 2370*mc 1238 + 2*mc 2370*mc 1183*mc 1238) + 2 * KeccakfPermAir.extraction.inter_6138 c row := by
    simp only [KeccakfPermAir.extraction.inter_6140, KeccakfPermAir.extraction.inter_6139, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6138 c row = (mc 2371 + mc 1239 - mc 1184*mc 1239 - 2*mc 2371*mc 1239 + 2*mc 2371*mc 1184*mc 1239) + 2 * KeccakfPermAir.extraction.inter_6136 c row := by
    simp only [KeccakfPermAir.extraction.inter_6138, KeccakfPermAir.extraction.inter_6137, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6136 c row = (mc 2372 + mc 1240 - mc 1121*mc 1240 - 2*mc 2372*mc 1240 + 2*mc 2372*mc 1121*mc 1240) + 2 * KeccakfPermAir.extraction.inter_6134 c row := by
    simp only [KeccakfPermAir.extraction.inter_6136, KeccakfPermAir.extraction.inter_6135, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6134 c row = (mc 2373 + mc 1241 - mc 1122*mc 1241 - 2*mc 2373*mc 1241 + 2*mc 2373*mc 1122*mc 1241) + 2 * KeccakfPermAir.extraction.inter_6132 c row := by
    simp only [KeccakfPermAir.extraction.inter_6134, KeccakfPermAir.extraction.inter_6133, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6132 c row = (mc 2374 + mc 1242 - mc 1123*mc 1242 - 2*mc 2374*mc 1242 + 2*mc 2374*mc 1123*mc 1242) + 2 * KeccakfPermAir.extraction.inter_6130 c row := by
    simp only [KeccakfPermAir.extraction.inter_6132, KeccakfPermAir.extraction.inter_6131, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6130 c row = (mc 2375 + mc 1243 - mc 1124*mc 1243 - 2*mc 2375*mc 1243 + 2*mc 2375*mc 1124*mc 1243) + 2 * KeccakfPermAir.extraction.inter_6128 c row := by
    simp only [KeccakfPermAir.extraction.inter_6130, KeccakfPermAir.extraction.inter_6129, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6128 c row = (mc 2376 + mc 1244 - mc 1125*mc 1244 - 2*mc 2376*mc 1244 + 2*mc 2376*mc 1125*mc 1244) := by
    simp only [KeccakfPermAir.extraction.inter_6128, KeccakfPermAir.extraction.inter_6127, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2988 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2988 c row) :
    ((mc 2377 + mc 1245 - mc 1126*mc 1245 - 2*mc 2377*mc 1245 + 2*mc 2377*mc 1126*mc 1245) + 2*(mc 2378 + mc 1246 - mc 1127*mc 1246 - 2*mc 2378*mc 1246 + 2*mc 2378*mc 1127*mc 1246) + 4*(mc 2379 + mc 1247 - mc 1128*mc 1247 - 2*mc 2379*mc 1247 + 2*mc 2379*mc 1128*mc 1247) + 8*(mc 2380 + mc 1248 - mc 1129*mc 1248 - 2*mc 2380*mc 1248 + 2*mc 2380*mc 1129*mc 1248) + 16*(mc 2381 + mc 1185 - mc 1130*mc 1185 - 2*mc 2381*mc 1185 + 2*mc 2381*mc 1130*mc 1185) + 32*(mc 2382 + mc 1186 - mc 1131*mc 1186 - 2*mc 2382*mc 1186 + 2*mc 2382*mc 1131*mc 1186) + 64*(mc 2383 + mc 1187 - mc 1132*mc 1187 - 2*mc 2383*mc 1187 + 2*mc 2383*mc 1132*mc 1187) + 128*(mc 2384 + mc 1188 - mc 1133*mc 1188 - 2*mc 2384*mc 1188 + 2*mc 2384*mc 1133*mc 1188) + 256*(mc 2385 + mc 1189 - mc 1134*mc 1189 - 2*mc 2385*mc 1189 + 2*mc 2385*mc 1134*mc 1189) + 512*(mc 2386 + mc 1190 - mc 1135*mc 1190 - 2*mc 2386*mc 1190 + 2*mc 2386*mc 1135*mc 1190) + 1024*(mc 2387 + mc 1191 - mc 1136*mc 1191 - 2*mc 2387*mc 1191 + 2*mc 2387*mc 1136*mc 1191) + 2048*(mc 2388 + mc 1192 - mc 1137*mc 1192 - 2*mc 2388*mc 1192 + 2*mc 2388*mc 1137*mc 1192) + 4096*(mc 2389 + mc 1193 - mc 1138*mc 1193 - 2*mc 2389*mc 1193 + 2*mc 2389*mc 1138*mc 1193) + 8192*(mc 2390 + mc 1194 - mc 1139*mc 1194 - 2*mc 2390*mc 1194 + 2*mc 2390*mc 1139*mc 1194) + 16384*(mc 2391 + mc 1195 - mc 1140*mc 1195 - 2*mc 2391*mc 1195 + 2*mc 2391*mc 1140*mc 1195) + 32768*(mc 2392 + mc 1196 - mc 1141*mc 1196 - 2*mc 2392*mc 1196 + 2*mc 2392*mc 1141*mc 1196)) - mc 2543 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2988, KeccakfPermAir.extraction.inter_6188, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6187 c row = (mc 2378 + mc 1246 - mc 1127*mc 1246 - 2*mc 2378*mc 1246 + 2*mc 2378*mc 1127*mc 1246) + 2 * KeccakfPermAir.extraction.inter_6185 c row := by
    simp only [KeccakfPermAir.extraction.inter_6187, KeccakfPermAir.extraction.inter_6186, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6185 c row = (mc 2379 + mc 1247 - mc 1128*mc 1247 - 2*mc 2379*mc 1247 + 2*mc 2379*mc 1128*mc 1247) + 2 * KeccakfPermAir.extraction.inter_6183 c row := by
    simp only [KeccakfPermAir.extraction.inter_6185, KeccakfPermAir.extraction.inter_6184, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6183 c row = (mc 2380 + mc 1248 - mc 1129*mc 1248 - 2*mc 2380*mc 1248 + 2*mc 2380*mc 1129*mc 1248) + 2 * KeccakfPermAir.extraction.inter_6181 c row := by
    simp only [KeccakfPermAir.extraction.inter_6183, KeccakfPermAir.extraction.inter_6182, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6181 c row = (mc 2381 + mc 1185 - mc 1130*mc 1185 - 2*mc 2381*mc 1185 + 2*mc 2381*mc 1130*mc 1185) + 2 * KeccakfPermAir.extraction.inter_6179 c row := by
    simp only [KeccakfPermAir.extraction.inter_6181, KeccakfPermAir.extraction.inter_6180, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6179 c row = (mc 2382 + mc 1186 - mc 1131*mc 1186 - 2*mc 2382*mc 1186 + 2*mc 2382*mc 1131*mc 1186) + 2 * KeccakfPermAir.extraction.inter_6177 c row := by
    simp only [KeccakfPermAir.extraction.inter_6179, KeccakfPermAir.extraction.inter_6178, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6177 c row = (mc 2383 + mc 1187 - mc 1132*mc 1187 - 2*mc 2383*mc 1187 + 2*mc 2383*mc 1132*mc 1187) + 2 * KeccakfPermAir.extraction.inter_6175 c row := by
    simp only [KeccakfPermAir.extraction.inter_6177, KeccakfPermAir.extraction.inter_6176, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6175 c row = (mc 2384 + mc 1188 - mc 1133*mc 1188 - 2*mc 2384*mc 1188 + 2*mc 2384*mc 1133*mc 1188) + 2 * KeccakfPermAir.extraction.inter_6173 c row := by
    simp only [KeccakfPermAir.extraction.inter_6175, KeccakfPermAir.extraction.inter_6174, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6173 c row = (mc 2385 + mc 1189 - mc 1134*mc 1189 - 2*mc 2385*mc 1189 + 2*mc 2385*mc 1134*mc 1189) + 2 * KeccakfPermAir.extraction.inter_6171 c row := by
    simp only [KeccakfPermAir.extraction.inter_6173, KeccakfPermAir.extraction.inter_6172, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6171 c row = (mc 2386 + mc 1190 - mc 1135*mc 1190 - 2*mc 2386*mc 1190 + 2*mc 2386*mc 1135*mc 1190) + 2 * KeccakfPermAir.extraction.inter_6169 c row := by
    simp only [KeccakfPermAir.extraction.inter_6171, KeccakfPermAir.extraction.inter_6170, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6169 c row = (mc 2387 + mc 1191 - mc 1136*mc 1191 - 2*mc 2387*mc 1191 + 2*mc 2387*mc 1136*mc 1191) + 2 * KeccakfPermAir.extraction.inter_6167 c row := by
    simp only [KeccakfPermAir.extraction.inter_6169, KeccakfPermAir.extraction.inter_6168, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6167 c row = (mc 2388 + mc 1192 - mc 1137*mc 1192 - 2*mc 2388*mc 1192 + 2*mc 2388*mc 1137*mc 1192) + 2 * KeccakfPermAir.extraction.inter_6165 c row := by
    simp only [KeccakfPermAir.extraction.inter_6167, KeccakfPermAir.extraction.inter_6166, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6165 c row = (mc 2389 + mc 1193 - mc 1138*mc 1193 - 2*mc 2389*mc 1193 + 2*mc 2389*mc 1138*mc 1193) + 2 * KeccakfPermAir.extraction.inter_6163 c row := by
    simp only [KeccakfPermAir.extraction.inter_6165, KeccakfPermAir.extraction.inter_6164, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6163 c row = (mc 2390 + mc 1194 - mc 1139*mc 1194 - 2*mc 2390*mc 1194 + 2*mc 2390*mc 1139*mc 1194) + 2 * KeccakfPermAir.extraction.inter_6161 c row := by
    simp only [KeccakfPermAir.extraction.inter_6163, KeccakfPermAir.extraction.inter_6162, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6161 c row = (mc 2391 + mc 1195 - mc 1140*mc 1195 - 2*mc 2391*mc 1195 + 2*mc 2391*mc 1140*mc 1195) + 2 * KeccakfPermAir.extraction.inter_6159 c row := by
    simp only [KeccakfPermAir.extraction.inter_6161, KeccakfPermAir.extraction.inter_6160, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6159 c row = (mc 2392 + mc 1196 - mc 1141*mc 1196 - 2*mc 2392*mc 1196 + 2*mc 2392*mc 1141*mc 1196) := by
    simp only [KeccakfPermAir.extraction.inter_6159, KeccakfPermAir.extraction.inter_6158, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2989 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2989 c row) :
    ((mc 2393 + mc 1197 - mc 1142*mc 1197 - 2*mc 2393*mc 1197 + 2*mc 2393*mc 1142*mc 1197) + 2*(mc 2394 + mc 1198 - mc 1143*mc 1198 - 2*mc 2394*mc 1198 + 2*mc 2394*mc 1143*mc 1198) + 4*(mc 2395 + mc 1199 - mc 1144*mc 1199 - 2*mc 2395*mc 1199 + 2*mc 2395*mc 1144*mc 1199) + 8*(mc 2396 + mc 1200 - mc 1145*mc 1200 - 2*mc 2396*mc 1200 + 2*mc 2396*mc 1145*mc 1200) + 16*(mc 2397 + mc 1201 - mc 1146*mc 1201 - 2*mc 2397*mc 1201 + 2*mc 2397*mc 1146*mc 1201) + 32*(mc 2398 + mc 1202 - mc 1147*mc 1202 - 2*mc 2398*mc 1202 + 2*mc 2398*mc 1147*mc 1202) + 64*(mc 2399 + mc 1203 - mc 1148*mc 1203 - 2*mc 2399*mc 1203 + 2*mc 2399*mc 1148*mc 1203) + 128*(mc 2400 + mc 1204 - mc 1149*mc 1204 - 2*mc 2400*mc 1204 + 2*mc 2400*mc 1149*mc 1204) + 256*(mc 2337 + mc 1205 - mc 1150*mc 1205 - 2*mc 2337*mc 1205 + 2*mc 2337*mc 1150*mc 1205) + 512*(mc 2338 + mc 1206 - mc 1151*mc 1206 - 2*mc 2338*mc 1206 + 2*mc 2338*mc 1151*mc 1206) + 1024*(mc 2339 + mc 1207 - mc 1152*mc 1207 - 2*mc 2339*mc 1207 + 2*mc 2339*mc 1152*mc 1207) + 2048*(mc 2340 + mc 1208 - mc 1153*mc 1208 - 2*mc 2340*mc 1208 + 2*mc 2340*mc 1153*mc 1208) + 4096*(mc 2341 + mc 1209 - mc 1154*mc 1209 - 2*mc 2341*mc 1209 + 2*mc 2341*mc 1154*mc 1209) + 8192*(mc 2342 + mc 1210 - mc 1155*mc 1210 - 2*mc 2342*mc 1210 + 2*mc 2342*mc 1155*mc 1210) + 16384*(mc 2343 + mc 1211 - mc 1156*mc 1211 - 2*mc 2343*mc 1211 + 2*mc 2343*mc 1156*mc 1211) + 32768*(mc 2344 + mc 1212 - mc 1157*mc 1212 - 2*mc 2344*mc 1212 + 2*mc 2344*mc 1157*mc 1212)) - mc 2544 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2989, KeccakfPermAir.extraction.inter_6219, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6218 c row = (mc 2394 + mc 1198 - mc 1143*mc 1198 - 2*mc 2394*mc 1198 + 2*mc 2394*mc 1143*mc 1198) + 2 * KeccakfPermAir.extraction.inter_6216 c row := by
    simp only [KeccakfPermAir.extraction.inter_6218, KeccakfPermAir.extraction.inter_6217, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6216 c row = (mc 2395 + mc 1199 - mc 1144*mc 1199 - 2*mc 2395*mc 1199 + 2*mc 2395*mc 1144*mc 1199) + 2 * KeccakfPermAir.extraction.inter_6214 c row := by
    simp only [KeccakfPermAir.extraction.inter_6216, KeccakfPermAir.extraction.inter_6215, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6214 c row = (mc 2396 + mc 1200 - mc 1145*mc 1200 - 2*mc 2396*mc 1200 + 2*mc 2396*mc 1145*mc 1200) + 2 * KeccakfPermAir.extraction.inter_6212 c row := by
    simp only [KeccakfPermAir.extraction.inter_6214, KeccakfPermAir.extraction.inter_6213, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6212 c row = (mc 2397 + mc 1201 - mc 1146*mc 1201 - 2*mc 2397*mc 1201 + 2*mc 2397*mc 1146*mc 1201) + 2 * KeccakfPermAir.extraction.inter_6210 c row := by
    simp only [KeccakfPermAir.extraction.inter_6212, KeccakfPermAir.extraction.inter_6211, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6210 c row = (mc 2398 + mc 1202 - mc 1147*mc 1202 - 2*mc 2398*mc 1202 + 2*mc 2398*mc 1147*mc 1202) + 2 * KeccakfPermAir.extraction.inter_6208 c row := by
    simp only [KeccakfPermAir.extraction.inter_6210, KeccakfPermAir.extraction.inter_6209, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6208 c row = (mc 2399 + mc 1203 - mc 1148*mc 1203 - 2*mc 2399*mc 1203 + 2*mc 2399*mc 1148*mc 1203) + 2 * KeccakfPermAir.extraction.inter_6206 c row := by
    simp only [KeccakfPermAir.extraction.inter_6208, KeccakfPermAir.extraction.inter_6207, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6206 c row = (mc 2400 + mc 1204 - mc 1149*mc 1204 - 2*mc 2400*mc 1204 + 2*mc 2400*mc 1149*mc 1204) + 2 * KeccakfPermAir.extraction.inter_6204 c row := by
    simp only [KeccakfPermAir.extraction.inter_6206, KeccakfPermAir.extraction.inter_6205, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6204 c row = (mc 2337 + mc 1205 - mc 1150*mc 1205 - 2*mc 2337*mc 1205 + 2*mc 2337*mc 1150*mc 1205) + 2 * KeccakfPermAir.extraction.inter_6202 c row := by
    simp only [KeccakfPermAir.extraction.inter_6204, KeccakfPermAir.extraction.inter_6203, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6202 c row = (mc 2338 + mc 1206 - mc 1151*mc 1206 - 2*mc 2338*mc 1206 + 2*mc 2338*mc 1151*mc 1206) + 2 * KeccakfPermAir.extraction.inter_6200 c row := by
    simp only [KeccakfPermAir.extraction.inter_6202, KeccakfPermAir.extraction.inter_6201, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6200 c row = (mc 2339 + mc 1207 - mc 1152*mc 1207 - 2*mc 2339*mc 1207 + 2*mc 2339*mc 1152*mc 1207) + 2 * KeccakfPermAir.extraction.inter_6198 c row := by
    simp only [KeccakfPermAir.extraction.inter_6200, KeccakfPermAir.extraction.inter_6199, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6198 c row = (mc 2340 + mc 1208 - mc 1153*mc 1208 - 2*mc 2340*mc 1208 + 2*mc 2340*mc 1153*mc 1208) + 2 * KeccakfPermAir.extraction.inter_6196 c row := by
    simp only [KeccakfPermAir.extraction.inter_6198, KeccakfPermAir.extraction.inter_6197, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6196 c row = (mc 2341 + mc 1209 - mc 1154*mc 1209 - 2*mc 2341*mc 1209 + 2*mc 2341*mc 1154*mc 1209) + 2 * KeccakfPermAir.extraction.inter_6194 c row := by
    simp only [KeccakfPermAir.extraction.inter_6196, KeccakfPermAir.extraction.inter_6195, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6194 c row = (mc 2342 + mc 1210 - mc 1155*mc 1210 - 2*mc 2342*mc 1210 + 2*mc 2342*mc 1155*mc 1210) + 2 * KeccakfPermAir.extraction.inter_6192 c row := by
    simp only [KeccakfPermAir.extraction.inter_6194, KeccakfPermAir.extraction.inter_6193, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6192 c row = (mc 2343 + mc 1211 - mc 1156*mc 1211 - 2*mc 2343*mc 1211 + 2*mc 2343*mc 1156*mc 1211) + 2 * KeccakfPermAir.extraction.inter_6190 c row := by
    simp only [KeccakfPermAir.extraction.inter_6192, KeccakfPermAir.extraction.inter_6191, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6190 c row = (mc 2344 + mc 1212 - mc 1157*mc 1212 - 2*mc 2344*mc 1212 + 2*mc 2344*mc 1157*mc 1212) := by
    simp only [KeccakfPermAir.extraction.inter_6190, KeccakfPermAir.extraction.inter_6189, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2990 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2990 c row) :
    ((mc 995 + mc 1786 - mc 1386*mc 1786 - 2*mc 995*mc 1786 + 2*mc 995*mc 1386*mc 1786) + 2*(mc 996 + mc 1787 - mc 1387*mc 1787 - 2*mc 996*mc 1787 + 2*mc 996*mc 1387*mc 1787) + 4*(mc 997 + mc 1788 - mc 1388*mc 1788 - 2*mc 997*mc 1788 + 2*mc 997*mc 1388*mc 1788) + 8*(mc 998 + mc 1789 - mc 1389*mc 1789 - 2*mc 998*mc 1789 + 2*mc 998*mc 1389*mc 1789) + 16*(mc 999 + mc 1790 - mc 1390*mc 1790 - 2*mc 999*mc 1790 + 2*mc 999*mc 1390*mc 1790) + 32*(mc 1000 + mc 1791 - mc 1391*mc 1791 - 2*mc 1000*mc 1791 + 2*mc 1000*mc 1391*mc 1791) + 64*(mc 1001 + mc 1792 - mc 1392*mc 1792 - 2*mc 1001*mc 1792 + 2*mc 1001*mc 1392*mc 1792) + 128*(mc 1002 + mc 1793 - mc 1393*mc 1793 - 2*mc 1002*mc 1793 + 2*mc 1002*mc 1393*mc 1793) + 256*(mc 1003 + mc 1794 - mc 1394*mc 1794 - 2*mc 1003*mc 1794 + 2*mc 1003*mc 1394*mc 1794) + 512*(mc 1004 + mc 1795 - mc 1395*mc 1795 - 2*mc 1004*mc 1795 + 2*mc 1004*mc 1395*mc 1795) + 1024*(mc 1005 + mc 1796 - mc 1396*mc 1796 - 2*mc 1005*mc 1796 + 2*mc 1005*mc 1396*mc 1796) + 2048*(mc 1006 + mc 1797 - mc 1397*mc 1797 - 2*mc 1006*mc 1797 + 2*mc 1006*mc 1397*mc 1797) + 4096*(mc 1007 + mc 1798 - mc 1398*mc 1798 - 2*mc 1007*mc 1798 + 2*mc 1007*mc 1398*mc 1798) + 8192*(mc 1008 + mc 1799 - mc 1399*mc 1799 - 2*mc 1008*mc 1799 + 2*mc 1008*mc 1399*mc 1799) + 16384*(mc 1009 + mc 1800 - mc 1400*mc 1800 - 2*mc 1009*mc 1800 + 2*mc 1009*mc 1400*mc 1800) + 32768*(mc 1010 + mc 1801 - mc 1401*mc 1801 - 2*mc 1010*mc 1801 + 2*mc 1010*mc 1401*mc 1801)) - mc 2545 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2990, KeccakfPermAir.extraction.inter_6250, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6249 c row = (mc 996 + mc 1787 - mc 1387*mc 1787 - 2*mc 996*mc 1787 + 2*mc 996*mc 1387*mc 1787) + 2 * KeccakfPermAir.extraction.inter_6247 c row := by
    simp only [KeccakfPermAir.extraction.inter_6249, KeccakfPermAir.extraction.inter_6248, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6247 c row = (mc 997 + mc 1788 - mc 1388*mc 1788 - 2*mc 997*mc 1788 + 2*mc 997*mc 1388*mc 1788) + 2 * KeccakfPermAir.extraction.inter_6245 c row := by
    simp only [KeccakfPermAir.extraction.inter_6247, KeccakfPermAir.extraction.inter_6246, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6245 c row = (mc 998 + mc 1789 - mc 1389*mc 1789 - 2*mc 998*mc 1789 + 2*mc 998*mc 1389*mc 1789) + 2 * KeccakfPermAir.extraction.inter_6243 c row := by
    simp only [KeccakfPermAir.extraction.inter_6245, KeccakfPermAir.extraction.inter_6244, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6243 c row = (mc 999 + mc 1790 - mc 1390*mc 1790 - 2*mc 999*mc 1790 + 2*mc 999*mc 1390*mc 1790) + 2 * KeccakfPermAir.extraction.inter_6241 c row := by
    simp only [KeccakfPermAir.extraction.inter_6243, KeccakfPermAir.extraction.inter_6242, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6241 c row = (mc 1000 + mc 1791 - mc 1391*mc 1791 - 2*mc 1000*mc 1791 + 2*mc 1000*mc 1391*mc 1791) + 2 * KeccakfPermAir.extraction.inter_6239 c row := by
    simp only [KeccakfPermAir.extraction.inter_6241, KeccakfPermAir.extraction.inter_6240, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6239 c row = (mc 1001 + mc 1792 - mc 1392*mc 1792 - 2*mc 1001*mc 1792 + 2*mc 1001*mc 1392*mc 1792) + 2 * KeccakfPermAir.extraction.inter_6237 c row := by
    simp only [KeccakfPermAir.extraction.inter_6239, KeccakfPermAir.extraction.inter_6238, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6237 c row = (mc 1002 + mc 1793 - mc 1393*mc 1793 - 2*mc 1002*mc 1793 + 2*mc 1002*mc 1393*mc 1793) + 2 * KeccakfPermAir.extraction.inter_6235 c row := by
    simp only [KeccakfPermAir.extraction.inter_6237, KeccakfPermAir.extraction.inter_6236, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6235 c row = (mc 1003 + mc 1794 - mc 1394*mc 1794 - 2*mc 1003*mc 1794 + 2*mc 1003*mc 1394*mc 1794) + 2 * KeccakfPermAir.extraction.inter_6233 c row := by
    simp only [KeccakfPermAir.extraction.inter_6235, KeccakfPermAir.extraction.inter_6234, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6233 c row = (mc 1004 + mc 1795 - mc 1395*mc 1795 - 2*mc 1004*mc 1795 + 2*mc 1004*mc 1395*mc 1795) + 2 * KeccakfPermAir.extraction.inter_6231 c row := by
    simp only [KeccakfPermAir.extraction.inter_6233, KeccakfPermAir.extraction.inter_6232, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6231 c row = (mc 1005 + mc 1796 - mc 1396*mc 1796 - 2*mc 1005*mc 1796 + 2*mc 1005*mc 1396*mc 1796) + 2 * KeccakfPermAir.extraction.inter_6229 c row := by
    simp only [KeccakfPermAir.extraction.inter_6231, KeccakfPermAir.extraction.inter_6230, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6229 c row = (mc 1006 + mc 1797 - mc 1397*mc 1797 - 2*mc 1006*mc 1797 + 2*mc 1006*mc 1397*mc 1797) + 2 * KeccakfPermAir.extraction.inter_6227 c row := by
    simp only [KeccakfPermAir.extraction.inter_6229, KeccakfPermAir.extraction.inter_6228, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6227 c row = (mc 1007 + mc 1798 - mc 1398*mc 1798 - 2*mc 1007*mc 1798 + 2*mc 1007*mc 1398*mc 1798) + 2 * KeccakfPermAir.extraction.inter_6225 c row := by
    simp only [KeccakfPermAir.extraction.inter_6227, KeccakfPermAir.extraction.inter_6226, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6225 c row = (mc 1008 + mc 1799 - mc 1399*mc 1799 - 2*mc 1008*mc 1799 + 2*mc 1008*mc 1399*mc 1799) + 2 * KeccakfPermAir.extraction.inter_6223 c row := by
    simp only [KeccakfPermAir.extraction.inter_6225, KeccakfPermAir.extraction.inter_6224, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6223 c row = (mc 1009 + mc 1800 - mc 1400*mc 1800 - 2*mc 1009*mc 1800 + 2*mc 1009*mc 1400*mc 1800) + 2 * KeccakfPermAir.extraction.inter_6221 c row := by
    simp only [KeccakfPermAir.extraction.inter_6223, KeccakfPermAir.extraction.inter_6222, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6221 c row = (mc 1010 + mc 1801 - mc 1401*mc 1801 - 2*mc 1010*mc 1801 + 2*mc 1010*mc 1401*mc 1801) := by
    simp only [KeccakfPermAir.extraction.inter_6221, KeccakfPermAir.extraction.inter_6220, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2991 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2991 c row) :
    ((mc 1011 + mc 1802 - mc 1402*mc 1802 - 2*mc 1011*mc 1802 + 2*mc 1011*mc 1402*mc 1802) + 2*(mc 1012 + mc 1803 - mc 1403*mc 1803 - 2*mc 1012*mc 1803 + 2*mc 1012*mc 1403*mc 1803) + 4*(mc 1013 + mc 1804 - mc 1404*mc 1804 - 2*mc 1013*mc 1804 + 2*mc 1013*mc 1404*mc 1804) + 8*(mc 1014 + mc 1805 - mc 1405*mc 1805 - 2*mc 1014*mc 1805 + 2*mc 1014*mc 1405*mc 1805) + 16*(mc 1015 + mc 1806 - mc 1406*mc 1806 - 2*mc 1015*mc 1806 + 2*mc 1015*mc 1406*mc 1806) + 32*(mc 1016 + mc 1807 - mc 1407*mc 1807 - 2*mc 1016*mc 1807 + 2*mc 1016*mc 1407*mc 1807) + 64*(mc 1017 + mc 1808 - mc 1408*mc 1808 - 2*mc 1017*mc 1808 + 2*mc 1017*mc 1408*mc 1808) + 128*(mc 1018 + mc 1809 - mc 1409*mc 1809 - 2*mc 1018*mc 1809 + 2*mc 1018*mc 1409*mc 1809) + 256*(mc 1019 + mc 1810 - mc 1410*mc 1810 - 2*mc 1019*mc 1810 + 2*mc 1019*mc 1410*mc 1810) + 512*(mc 1020 + mc 1811 - mc 1411*mc 1811 - 2*mc 1020*mc 1811 + 2*mc 1020*mc 1411*mc 1811) + 1024*(mc 1021 + mc 1812 - mc 1412*mc 1812 - 2*mc 1021*mc 1812 + 2*mc 1021*mc 1412*mc 1812) + 2048*(mc 1022 + mc 1813 - mc 1413*mc 1813 - 2*mc 1022*mc 1813 + 2*mc 1022*mc 1413*mc 1813) + 4096*(mc 1023 + mc 1814 - mc 1414*mc 1814 - 2*mc 1023*mc 1814 + 2*mc 1023*mc 1414*mc 1814) + 8192*(mc 1024 + mc 1815 - mc 1415*mc 1815 - 2*mc 1024*mc 1815 + 2*mc 1024*mc 1415*mc 1815) + 16384*(mc 1025 + mc 1816 - mc 1416*mc 1816 - 2*mc 1025*mc 1816 + 2*mc 1025*mc 1416*mc 1816) + 32768*(mc 1026 + mc 1817 - mc 1417*mc 1817 - 2*mc 1026*mc 1817 + 2*mc 1026*mc 1417*mc 1817)) - mc 2546 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2991, KeccakfPermAir.extraction.inter_6281, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6280 c row = (mc 1012 + mc 1803 - mc 1403*mc 1803 - 2*mc 1012*mc 1803 + 2*mc 1012*mc 1403*mc 1803) + 2 * KeccakfPermAir.extraction.inter_6278 c row := by
    simp only [KeccakfPermAir.extraction.inter_6280, KeccakfPermAir.extraction.inter_6279, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6278 c row = (mc 1013 + mc 1804 - mc 1404*mc 1804 - 2*mc 1013*mc 1804 + 2*mc 1013*mc 1404*mc 1804) + 2 * KeccakfPermAir.extraction.inter_6276 c row := by
    simp only [KeccakfPermAir.extraction.inter_6278, KeccakfPermAir.extraction.inter_6277, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6276 c row = (mc 1014 + mc 1805 - mc 1405*mc 1805 - 2*mc 1014*mc 1805 + 2*mc 1014*mc 1405*mc 1805) + 2 * KeccakfPermAir.extraction.inter_6274 c row := by
    simp only [KeccakfPermAir.extraction.inter_6276, KeccakfPermAir.extraction.inter_6275, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6274 c row = (mc 1015 + mc 1806 - mc 1406*mc 1806 - 2*mc 1015*mc 1806 + 2*mc 1015*mc 1406*mc 1806) + 2 * KeccakfPermAir.extraction.inter_6272 c row := by
    simp only [KeccakfPermAir.extraction.inter_6274, KeccakfPermAir.extraction.inter_6273, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6272 c row = (mc 1016 + mc 1807 - mc 1407*mc 1807 - 2*mc 1016*mc 1807 + 2*mc 1016*mc 1407*mc 1807) + 2 * KeccakfPermAir.extraction.inter_6270 c row := by
    simp only [KeccakfPermAir.extraction.inter_6272, KeccakfPermAir.extraction.inter_6271, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6270 c row = (mc 1017 + mc 1808 - mc 1408*mc 1808 - 2*mc 1017*mc 1808 + 2*mc 1017*mc 1408*mc 1808) + 2 * KeccakfPermAir.extraction.inter_6268 c row := by
    simp only [KeccakfPermAir.extraction.inter_6270, KeccakfPermAir.extraction.inter_6269, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6268 c row = (mc 1018 + mc 1809 - mc 1409*mc 1809 - 2*mc 1018*mc 1809 + 2*mc 1018*mc 1409*mc 1809) + 2 * KeccakfPermAir.extraction.inter_6266 c row := by
    simp only [KeccakfPermAir.extraction.inter_6268, KeccakfPermAir.extraction.inter_6267, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6266 c row = (mc 1019 + mc 1810 - mc 1410*mc 1810 - 2*mc 1019*mc 1810 + 2*mc 1019*mc 1410*mc 1810) + 2 * KeccakfPermAir.extraction.inter_6264 c row := by
    simp only [KeccakfPermAir.extraction.inter_6266, KeccakfPermAir.extraction.inter_6265, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6264 c row = (mc 1020 + mc 1811 - mc 1411*mc 1811 - 2*mc 1020*mc 1811 + 2*mc 1020*mc 1411*mc 1811) + 2 * KeccakfPermAir.extraction.inter_6262 c row := by
    simp only [KeccakfPermAir.extraction.inter_6264, KeccakfPermAir.extraction.inter_6263, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6262 c row = (mc 1021 + mc 1812 - mc 1412*mc 1812 - 2*mc 1021*mc 1812 + 2*mc 1021*mc 1412*mc 1812) + 2 * KeccakfPermAir.extraction.inter_6260 c row := by
    simp only [KeccakfPermAir.extraction.inter_6262, KeccakfPermAir.extraction.inter_6261, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6260 c row = (mc 1022 + mc 1813 - mc 1413*mc 1813 - 2*mc 1022*mc 1813 + 2*mc 1022*mc 1413*mc 1813) + 2 * KeccakfPermAir.extraction.inter_6258 c row := by
    simp only [KeccakfPermAir.extraction.inter_6260, KeccakfPermAir.extraction.inter_6259, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6258 c row = (mc 1023 + mc 1814 - mc 1414*mc 1814 - 2*mc 1023*mc 1814 + 2*mc 1023*mc 1414*mc 1814) + 2 * KeccakfPermAir.extraction.inter_6256 c row := by
    simp only [KeccakfPermAir.extraction.inter_6258, KeccakfPermAir.extraction.inter_6257, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6256 c row = (mc 1024 + mc 1815 - mc 1415*mc 1815 - 2*mc 1024*mc 1815 + 2*mc 1024*mc 1415*mc 1815) + 2 * KeccakfPermAir.extraction.inter_6254 c row := by
    simp only [KeccakfPermAir.extraction.inter_6256, KeccakfPermAir.extraction.inter_6255, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6254 c row = (mc 1025 + mc 1816 - mc 1416*mc 1816 - 2*mc 1025*mc 1816 + 2*mc 1025*mc 1416*mc 1816) + 2 * KeccakfPermAir.extraction.inter_6252 c row := by
    simp only [KeccakfPermAir.extraction.inter_6254, KeccakfPermAir.extraction.inter_6253, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6252 c row = (mc 1026 + mc 1817 - mc 1417*mc 1817 - 2*mc 1026*mc 1817 + 2*mc 1026*mc 1417*mc 1817) := by
    simp only [KeccakfPermAir.extraction.inter_6252, KeccakfPermAir.extraction.inter_6251, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2992 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2992 c row) :
    ((mc 1027 + mc 1818 - mc 1418*mc 1818 - 2*mc 1027*mc 1818 + 2*mc 1027*mc 1418*mc 1818) + 2*(mc 1028 + mc 1819 - mc 1419*mc 1819 - 2*mc 1028*mc 1819 + 2*mc 1028*mc 1419*mc 1819) + 4*(mc 1029 + mc 1820 - mc 1420*mc 1820 - 2*mc 1029*mc 1820 + 2*mc 1029*mc 1420*mc 1820) + 8*(mc 1030 + mc 1821 - mc 1421*mc 1821 - 2*mc 1030*mc 1821 + 2*mc 1030*mc 1421*mc 1821) + 16*(mc 1031 + mc 1822 - mc 1422*mc 1822 - 2*mc 1031*mc 1822 + 2*mc 1031*mc 1422*mc 1822) + 32*(mc 1032 + mc 1823 - mc 1423*mc 1823 - 2*mc 1032*mc 1823 + 2*mc 1032*mc 1423*mc 1823) + 64*(mc 1033 + mc 1824 - mc 1424*mc 1824 - 2*mc 1033*mc 1824 + 2*mc 1033*mc 1424*mc 1824) + 128*(mc 1034 + mc 1761 - mc 1425*mc 1761 - 2*mc 1034*mc 1761 + 2*mc 1034*mc 1425*mc 1761) + 256*(mc 1035 + mc 1762 - mc 1426*mc 1762 - 2*mc 1035*mc 1762 + 2*mc 1035*mc 1426*mc 1762) + 512*(mc 1036 + mc 1763 - mc 1427*mc 1763 - 2*mc 1036*mc 1763 + 2*mc 1036*mc 1427*mc 1763) + 1024*(mc 1037 + mc 1764 - mc 1428*mc 1764 - 2*mc 1037*mc 1764 + 2*mc 1037*mc 1428*mc 1764) + 2048*(mc 1038 + mc 1765 - mc 1429*mc 1765 - 2*mc 1038*mc 1765 + 2*mc 1038*mc 1429*mc 1765) + 4096*(mc 1039 + mc 1766 - mc 1430*mc 1766 - 2*mc 1039*mc 1766 + 2*mc 1039*mc 1430*mc 1766) + 8192*(mc 1040 + mc 1767 - mc 1431*mc 1767 - 2*mc 1040*mc 1767 + 2*mc 1040*mc 1431*mc 1767) + 16384*(mc 1041 + mc 1768 - mc 1432*mc 1768 - 2*mc 1041*mc 1768 + 2*mc 1041*mc 1432*mc 1768) + 32768*(mc 1042 + mc 1769 - mc 1433*mc 1769 - 2*mc 1042*mc 1769 + 2*mc 1042*mc 1433*mc 1769)) - mc 2547 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2992, KeccakfPermAir.extraction.inter_6312, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6311 c row = (mc 1028 + mc 1819 - mc 1419*mc 1819 - 2*mc 1028*mc 1819 + 2*mc 1028*mc 1419*mc 1819) + 2 * KeccakfPermAir.extraction.inter_6309 c row := by
    simp only [KeccakfPermAir.extraction.inter_6311, KeccakfPermAir.extraction.inter_6310, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6309 c row = (mc 1029 + mc 1820 - mc 1420*mc 1820 - 2*mc 1029*mc 1820 + 2*mc 1029*mc 1420*mc 1820) + 2 * KeccakfPermAir.extraction.inter_6307 c row := by
    simp only [KeccakfPermAir.extraction.inter_6309, KeccakfPermAir.extraction.inter_6308, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6307 c row = (mc 1030 + mc 1821 - mc 1421*mc 1821 - 2*mc 1030*mc 1821 + 2*mc 1030*mc 1421*mc 1821) + 2 * KeccakfPermAir.extraction.inter_6305 c row := by
    simp only [KeccakfPermAir.extraction.inter_6307, KeccakfPermAir.extraction.inter_6306, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6305 c row = (mc 1031 + mc 1822 - mc 1422*mc 1822 - 2*mc 1031*mc 1822 + 2*mc 1031*mc 1422*mc 1822) + 2 * KeccakfPermAir.extraction.inter_6303 c row := by
    simp only [KeccakfPermAir.extraction.inter_6305, KeccakfPermAir.extraction.inter_6304, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6303 c row = (mc 1032 + mc 1823 - mc 1423*mc 1823 - 2*mc 1032*mc 1823 + 2*mc 1032*mc 1423*mc 1823) + 2 * KeccakfPermAir.extraction.inter_6301 c row := by
    simp only [KeccakfPermAir.extraction.inter_6303, KeccakfPermAir.extraction.inter_6302, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6301 c row = (mc 1033 + mc 1824 - mc 1424*mc 1824 - 2*mc 1033*mc 1824 + 2*mc 1033*mc 1424*mc 1824) + 2 * KeccakfPermAir.extraction.inter_6299 c row := by
    simp only [KeccakfPermAir.extraction.inter_6301, KeccakfPermAir.extraction.inter_6300, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6299 c row = (mc 1034 + mc 1761 - mc 1425*mc 1761 - 2*mc 1034*mc 1761 + 2*mc 1034*mc 1425*mc 1761) + 2 * KeccakfPermAir.extraction.inter_6297 c row := by
    simp only [KeccakfPermAir.extraction.inter_6299, KeccakfPermAir.extraction.inter_6298, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6297 c row = (mc 1035 + mc 1762 - mc 1426*mc 1762 - 2*mc 1035*mc 1762 + 2*mc 1035*mc 1426*mc 1762) + 2 * KeccakfPermAir.extraction.inter_6295 c row := by
    simp only [KeccakfPermAir.extraction.inter_6297, KeccakfPermAir.extraction.inter_6296, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6295 c row = (mc 1036 + mc 1763 - mc 1427*mc 1763 - 2*mc 1036*mc 1763 + 2*mc 1036*mc 1427*mc 1763) + 2 * KeccakfPermAir.extraction.inter_6293 c row := by
    simp only [KeccakfPermAir.extraction.inter_6295, KeccakfPermAir.extraction.inter_6294, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6293 c row = (mc 1037 + mc 1764 - mc 1428*mc 1764 - 2*mc 1037*mc 1764 + 2*mc 1037*mc 1428*mc 1764) + 2 * KeccakfPermAir.extraction.inter_6291 c row := by
    simp only [KeccakfPermAir.extraction.inter_6293, KeccakfPermAir.extraction.inter_6292, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6291 c row = (mc 1038 + mc 1765 - mc 1429*mc 1765 - 2*mc 1038*mc 1765 + 2*mc 1038*mc 1429*mc 1765) + 2 * KeccakfPermAir.extraction.inter_6289 c row := by
    simp only [KeccakfPermAir.extraction.inter_6291, KeccakfPermAir.extraction.inter_6290, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6289 c row = (mc 1039 + mc 1766 - mc 1430*mc 1766 - 2*mc 1039*mc 1766 + 2*mc 1039*mc 1430*mc 1766) + 2 * KeccakfPermAir.extraction.inter_6287 c row := by
    simp only [KeccakfPermAir.extraction.inter_6289, KeccakfPermAir.extraction.inter_6288, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6287 c row = (mc 1040 + mc 1767 - mc 1431*mc 1767 - 2*mc 1040*mc 1767 + 2*mc 1040*mc 1431*mc 1767) + 2 * KeccakfPermAir.extraction.inter_6285 c row := by
    simp only [KeccakfPermAir.extraction.inter_6287, KeccakfPermAir.extraction.inter_6286, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6285 c row = (mc 1041 + mc 1768 - mc 1432*mc 1768 - 2*mc 1041*mc 1768 + 2*mc 1041*mc 1432*mc 1768) + 2 * KeccakfPermAir.extraction.inter_6283 c row := by
    simp only [KeccakfPermAir.extraction.inter_6285, KeccakfPermAir.extraction.inter_6284, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6283 c row = (mc 1042 + mc 1769 - mc 1433*mc 1769 - 2*mc 1042*mc 1769 + 2*mc 1042*mc 1433*mc 1769) := by
    simp only [KeccakfPermAir.extraction.inter_6283, KeccakfPermAir.extraction.inter_6282, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2993 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2993 c row) :
    ((mc 1043 + mc 1770 - mc 1434*mc 1770 - 2*mc 1043*mc 1770 + 2*mc 1043*mc 1434*mc 1770) + 2*(mc 1044 + mc 1771 - mc 1435*mc 1771 - 2*mc 1044*mc 1771 + 2*mc 1044*mc 1435*mc 1771) + 4*(mc 1045 + mc 1772 - mc 1436*mc 1772 - 2*mc 1045*mc 1772 + 2*mc 1045*mc 1436*mc 1772) + 8*(mc 1046 + mc 1773 - mc 1437*mc 1773 - 2*mc 1046*mc 1773 + 2*mc 1046*mc 1437*mc 1773) + 16*(mc 1047 + mc 1774 - mc 1438*mc 1774 - 2*mc 1047*mc 1774 + 2*mc 1047*mc 1438*mc 1774) + 32*(mc 1048 + mc 1775 - mc 1439*mc 1775 - 2*mc 1048*mc 1775 + 2*mc 1048*mc 1439*mc 1775) + 64*(mc 1049 + mc 1776 - mc 1440*mc 1776 - 2*mc 1049*mc 1776 + 2*mc 1049*mc 1440*mc 1776) + 128*(mc 1050 + mc 1777 - mc 1377*mc 1777 - 2*mc 1050*mc 1777 + 2*mc 1050*mc 1377*mc 1777) + 256*(mc 1051 + mc 1778 - mc 1378*mc 1778 - 2*mc 1051*mc 1778 + 2*mc 1051*mc 1378*mc 1778) + 512*(mc 1052 + mc 1779 - mc 1379*mc 1779 - 2*mc 1052*mc 1779 + 2*mc 1052*mc 1379*mc 1779) + 1024*(mc 1053 + mc 1780 - mc 1380*mc 1780 - 2*mc 1053*mc 1780 + 2*mc 1053*mc 1380*mc 1780) + 2048*(mc 1054 + mc 1781 - mc 1381*mc 1781 - 2*mc 1054*mc 1781 + 2*mc 1054*mc 1381*mc 1781) + 4096*(mc 1055 + mc 1782 - mc 1382*mc 1782 - 2*mc 1055*mc 1782 + 2*mc 1055*mc 1382*mc 1782) + 8192*(mc 1056 + mc 1783 - mc 1383*mc 1783 - 2*mc 1056*mc 1783 + 2*mc 1056*mc 1383*mc 1783) + 16384*(mc 993 + mc 1784 - mc 1384*mc 1784 - 2*mc 993*mc 1784 + 2*mc 993*mc 1384*mc 1784) + 32768*(mc 994 + mc 1785 - mc 1385*mc 1785 - 2*mc 994*mc 1785 + 2*mc 994*mc 1385*mc 1785)) - mc 2548 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2993, KeccakfPermAir.extraction.inter_6343, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6342 c row = (mc 1044 + mc 1771 - mc 1435*mc 1771 - 2*mc 1044*mc 1771 + 2*mc 1044*mc 1435*mc 1771) + 2 * KeccakfPermAir.extraction.inter_6340 c row := by
    simp only [KeccakfPermAir.extraction.inter_6342, KeccakfPermAir.extraction.inter_6341, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6340 c row = (mc 1045 + mc 1772 - mc 1436*mc 1772 - 2*mc 1045*mc 1772 + 2*mc 1045*mc 1436*mc 1772) + 2 * KeccakfPermAir.extraction.inter_6338 c row := by
    simp only [KeccakfPermAir.extraction.inter_6340, KeccakfPermAir.extraction.inter_6339, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6338 c row = (mc 1046 + mc 1773 - mc 1437*mc 1773 - 2*mc 1046*mc 1773 + 2*mc 1046*mc 1437*mc 1773) + 2 * KeccakfPermAir.extraction.inter_6336 c row := by
    simp only [KeccakfPermAir.extraction.inter_6338, KeccakfPermAir.extraction.inter_6337, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6336 c row = (mc 1047 + mc 1774 - mc 1438*mc 1774 - 2*mc 1047*mc 1774 + 2*mc 1047*mc 1438*mc 1774) + 2 * KeccakfPermAir.extraction.inter_6334 c row := by
    simp only [KeccakfPermAir.extraction.inter_6336, KeccakfPermAir.extraction.inter_6335, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6334 c row = (mc 1048 + mc 1775 - mc 1439*mc 1775 - 2*mc 1048*mc 1775 + 2*mc 1048*mc 1439*mc 1775) + 2 * KeccakfPermAir.extraction.inter_6332 c row := by
    simp only [KeccakfPermAir.extraction.inter_6334, KeccakfPermAir.extraction.inter_6333, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6332 c row = (mc 1049 + mc 1776 - mc 1440*mc 1776 - 2*mc 1049*mc 1776 + 2*mc 1049*mc 1440*mc 1776) + 2 * KeccakfPermAir.extraction.inter_6330 c row := by
    simp only [KeccakfPermAir.extraction.inter_6332, KeccakfPermAir.extraction.inter_6331, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6330 c row = (mc 1050 + mc 1777 - mc 1377*mc 1777 - 2*mc 1050*mc 1777 + 2*mc 1050*mc 1377*mc 1777) + 2 * KeccakfPermAir.extraction.inter_6328 c row := by
    simp only [KeccakfPermAir.extraction.inter_6330, KeccakfPermAir.extraction.inter_6329, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6328 c row = (mc 1051 + mc 1778 - mc 1378*mc 1778 - 2*mc 1051*mc 1778 + 2*mc 1051*mc 1378*mc 1778) + 2 * KeccakfPermAir.extraction.inter_6326 c row := by
    simp only [KeccakfPermAir.extraction.inter_6328, KeccakfPermAir.extraction.inter_6327, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6326 c row = (mc 1052 + mc 1779 - mc 1379*mc 1779 - 2*mc 1052*mc 1779 + 2*mc 1052*mc 1379*mc 1779) + 2 * KeccakfPermAir.extraction.inter_6324 c row := by
    simp only [KeccakfPermAir.extraction.inter_6326, KeccakfPermAir.extraction.inter_6325, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6324 c row = (mc 1053 + mc 1780 - mc 1380*mc 1780 - 2*mc 1053*mc 1780 + 2*mc 1053*mc 1380*mc 1780) + 2 * KeccakfPermAir.extraction.inter_6322 c row := by
    simp only [KeccakfPermAir.extraction.inter_6324, KeccakfPermAir.extraction.inter_6323, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6322 c row = (mc 1054 + mc 1781 - mc 1381*mc 1781 - 2*mc 1054*mc 1781 + 2*mc 1054*mc 1381*mc 1781) + 2 * KeccakfPermAir.extraction.inter_6320 c row := by
    simp only [KeccakfPermAir.extraction.inter_6322, KeccakfPermAir.extraction.inter_6321, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6320 c row = (mc 1055 + mc 1782 - mc 1382*mc 1782 - 2*mc 1055*mc 1782 + 2*mc 1055*mc 1382*mc 1782) + 2 * KeccakfPermAir.extraction.inter_6318 c row := by
    simp only [KeccakfPermAir.extraction.inter_6320, KeccakfPermAir.extraction.inter_6319, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6318 c row = (mc 1056 + mc 1783 - mc 1383*mc 1783 - 2*mc 1056*mc 1783 + 2*mc 1056*mc 1383*mc 1783) + 2 * KeccakfPermAir.extraction.inter_6316 c row := by
    simp only [KeccakfPermAir.extraction.inter_6318, KeccakfPermAir.extraction.inter_6317, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6316 c row = (mc 993 + mc 1784 - mc 1384*mc 1784 - 2*mc 993*mc 1784 + 2*mc 993*mc 1384*mc 1784) + 2 * KeccakfPermAir.extraction.inter_6314 c row := by
    simp only [KeccakfPermAir.extraction.inter_6316, KeccakfPermAir.extraction.inter_6315, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6314 c row = (mc 994 + mc 1785 - mc 1385*mc 1785 - 2*mc 994*mc 1785 + 2*mc 994*mc 1385*mc 1785) := by
    simp only [KeccakfPermAir.extraction.inter_6314, KeccakfPermAir.extraction.inter_6313, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2994 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2994 c row) :
    ((mc 1386 + mc 1848 - mc 1786*mc 1848 - 2*mc 1386*mc 1848 + 2*mc 1386*mc 1786*mc 1848) + 2*(mc 1387 + mc 1849 - mc 1787*mc 1849 - 2*mc 1387*mc 1849 + 2*mc 1387*mc 1787*mc 1849) + 4*(mc 1388 + mc 1850 - mc 1788*mc 1850 - 2*mc 1388*mc 1850 + 2*mc 1388*mc 1788*mc 1850) + 8*(mc 1389 + mc 1851 - mc 1789*mc 1851 - 2*mc 1389*mc 1851 + 2*mc 1389*mc 1789*mc 1851) + 16*(mc 1390 + mc 1852 - mc 1790*mc 1852 - 2*mc 1390*mc 1852 + 2*mc 1390*mc 1790*mc 1852) + 32*(mc 1391 + mc 1853 - mc 1791*mc 1853 - 2*mc 1391*mc 1853 + 2*mc 1391*mc 1791*mc 1853) + 64*(mc 1392 + mc 1854 - mc 1792*mc 1854 - 2*mc 1392*mc 1854 + 2*mc 1392*mc 1792*mc 1854) + 128*(mc 1393 + mc 1855 - mc 1793*mc 1855 - 2*mc 1393*mc 1855 + 2*mc 1393*mc 1793*mc 1855) + 256*(mc 1394 + mc 1856 - mc 1794*mc 1856 - 2*mc 1394*mc 1856 + 2*mc 1394*mc 1794*mc 1856) + 512*(mc 1395 + mc 1857 - mc 1795*mc 1857 - 2*mc 1395*mc 1857 + 2*mc 1395*mc 1795*mc 1857) + 1024*(mc 1396 + mc 1858 - mc 1796*mc 1858 - 2*mc 1396*mc 1858 + 2*mc 1396*mc 1796*mc 1858) + 2048*(mc 1397 + mc 1859 - mc 1797*mc 1859 - 2*mc 1397*mc 1859 + 2*mc 1397*mc 1797*mc 1859) + 4096*(mc 1398 + mc 1860 - mc 1798*mc 1860 - 2*mc 1398*mc 1860 + 2*mc 1398*mc 1798*mc 1860) + 8192*(mc 1399 + mc 1861 - mc 1799*mc 1861 - 2*mc 1399*mc 1861 + 2*mc 1399*mc 1799*mc 1861) + 16384*(mc 1400 + mc 1862 - mc 1800*mc 1862 - 2*mc 1400*mc 1862 + 2*mc 1400*mc 1800*mc 1862) + 32768*(mc 1401 + mc 1863 - mc 1801*mc 1863 - 2*mc 1401*mc 1863 + 2*mc 1401*mc 1801*mc 1863)) - mc 2549 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2994, KeccakfPermAir.extraction.inter_6374, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6373 c row = (mc 1387 + mc 1849 - mc 1787*mc 1849 - 2*mc 1387*mc 1849 + 2*mc 1387*mc 1787*mc 1849) + 2 * KeccakfPermAir.extraction.inter_6371 c row := by
    simp only [KeccakfPermAir.extraction.inter_6373, KeccakfPermAir.extraction.inter_6372, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6371 c row = (mc 1388 + mc 1850 - mc 1788*mc 1850 - 2*mc 1388*mc 1850 + 2*mc 1388*mc 1788*mc 1850) + 2 * KeccakfPermAir.extraction.inter_6369 c row := by
    simp only [KeccakfPermAir.extraction.inter_6371, KeccakfPermAir.extraction.inter_6370, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6369 c row = (mc 1389 + mc 1851 - mc 1789*mc 1851 - 2*mc 1389*mc 1851 + 2*mc 1389*mc 1789*mc 1851) + 2 * KeccakfPermAir.extraction.inter_6367 c row := by
    simp only [KeccakfPermAir.extraction.inter_6369, KeccakfPermAir.extraction.inter_6368, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6367 c row = (mc 1390 + mc 1852 - mc 1790*mc 1852 - 2*mc 1390*mc 1852 + 2*mc 1390*mc 1790*mc 1852) + 2 * KeccakfPermAir.extraction.inter_6365 c row := by
    simp only [KeccakfPermAir.extraction.inter_6367, KeccakfPermAir.extraction.inter_6366, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6365 c row = (mc 1391 + mc 1853 - mc 1791*mc 1853 - 2*mc 1391*mc 1853 + 2*mc 1391*mc 1791*mc 1853) + 2 * KeccakfPermAir.extraction.inter_6363 c row := by
    simp only [KeccakfPermAir.extraction.inter_6365, KeccakfPermAir.extraction.inter_6364, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6363 c row = (mc 1392 + mc 1854 - mc 1792*mc 1854 - 2*mc 1392*mc 1854 + 2*mc 1392*mc 1792*mc 1854) + 2 * KeccakfPermAir.extraction.inter_6361 c row := by
    simp only [KeccakfPermAir.extraction.inter_6363, KeccakfPermAir.extraction.inter_6362, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6361 c row = (mc 1393 + mc 1855 - mc 1793*mc 1855 - 2*mc 1393*mc 1855 + 2*mc 1393*mc 1793*mc 1855) + 2 * KeccakfPermAir.extraction.inter_6359 c row := by
    simp only [KeccakfPermAir.extraction.inter_6361, KeccakfPermAir.extraction.inter_6360, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6359 c row = (mc 1394 + mc 1856 - mc 1794*mc 1856 - 2*mc 1394*mc 1856 + 2*mc 1394*mc 1794*mc 1856) + 2 * KeccakfPermAir.extraction.inter_6357 c row := by
    simp only [KeccakfPermAir.extraction.inter_6359, KeccakfPermAir.extraction.inter_6358, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6357 c row = (mc 1395 + mc 1857 - mc 1795*mc 1857 - 2*mc 1395*mc 1857 + 2*mc 1395*mc 1795*mc 1857) + 2 * KeccakfPermAir.extraction.inter_6355 c row := by
    simp only [KeccakfPermAir.extraction.inter_6357, KeccakfPermAir.extraction.inter_6356, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6355 c row = (mc 1396 + mc 1858 - mc 1796*mc 1858 - 2*mc 1396*mc 1858 + 2*mc 1396*mc 1796*mc 1858) + 2 * KeccakfPermAir.extraction.inter_6353 c row := by
    simp only [KeccakfPermAir.extraction.inter_6355, KeccakfPermAir.extraction.inter_6354, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6353 c row = (mc 1397 + mc 1859 - mc 1797*mc 1859 - 2*mc 1397*mc 1859 + 2*mc 1397*mc 1797*mc 1859) + 2 * KeccakfPermAir.extraction.inter_6351 c row := by
    simp only [KeccakfPermAir.extraction.inter_6353, KeccakfPermAir.extraction.inter_6352, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6351 c row = (mc 1398 + mc 1860 - mc 1798*mc 1860 - 2*mc 1398*mc 1860 + 2*mc 1398*mc 1798*mc 1860) + 2 * KeccakfPermAir.extraction.inter_6349 c row := by
    simp only [KeccakfPermAir.extraction.inter_6351, KeccakfPermAir.extraction.inter_6350, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6349 c row = (mc 1399 + mc 1861 - mc 1799*mc 1861 - 2*mc 1399*mc 1861 + 2*mc 1399*mc 1799*mc 1861) + 2 * KeccakfPermAir.extraction.inter_6347 c row := by
    simp only [KeccakfPermAir.extraction.inter_6349, KeccakfPermAir.extraction.inter_6348, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6347 c row = (mc 1400 + mc 1862 - mc 1800*mc 1862 - 2*mc 1400*mc 1862 + 2*mc 1400*mc 1800*mc 1862) + 2 * KeccakfPermAir.extraction.inter_6345 c row := by
    simp only [KeccakfPermAir.extraction.inter_6347, KeccakfPermAir.extraction.inter_6346, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6345 c row = (mc 1401 + mc 1863 - mc 1801*mc 1863 - 2*mc 1401*mc 1863 + 2*mc 1401*mc 1801*mc 1863) := by
    simp only [KeccakfPermAir.extraction.inter_6345, KeccakfPermAir.extraction.inter_6344, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2995 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2995 c row) :
    ((mc 1402 + mc 1864 - mc 1802*mc 1864 - 2*mc 1402*mc 1864 + 2*mc 1402*mc 1802*mc 1864) + 2*(mc 1403 + mc 1865 - mc 1803*mc 1865 - 2*mc 1403*mc 1865 + 2*mc 1403*mc 1803*mc 1865) + 4*(mc 1404 + mc 1866 - mc 1804*mc 1866 - 2*mc 1404*mc 1866 + 2*mc 1404*mc 1804*mc 1866) + 8*(mc 1405 + mc 1867 - mc 1805*mc 1867 - 2*mc 1405*mc 1867 + 2*mc 1405*mc 1805*mc 1867) + 16*(mc 1406 + mc 1868 - mc 1806*mc 1868 - 2*mc 1406*mc 1868 + 2*mc 1406*mc 1806*mc 1868) + 32*(mc 1407 + mc 1869 - mc 1807*mc 1869 - 2*mc 1407*mc 1869 + 2*mc 1407*mc 1807*mc 1869) + 64*(mc 1408 + mc 1870 - mc 1808*mc 1870 - 2*mc 1408*mc 1870 + 2*mc 1408*mc 1808*mc 1870) + 128*(mc 1409 + mc 1871 - mc 1809*mc 1871 - 2*mc 1409*mc 1871 + 2*mc 1409*mc 1809*mc 1871) + 256*(mc 1410 + mc 1872 - mc 1810*mc 1872 - 2*mc 1410*mc 1872 + 2*mc 1410*mc 1810*mc 1872) + 512*(mc 1411 + mc 1873 - mc 1811*mc 1873 - 2*mc 1411*mc 1873 + 2*mc 1411*mc 1811*mc 1873) + 1024*(mc 1412 + mc 1874 - mc 1812*mc 1874 - 2*mc 1412*mc 1874 + 2*mc 1412*mc 1812*mc 1874) + 2048*(mc 1413 + mc 1875 - mc 1813*mc 1875 - 2*mc 1413*mc 1875 + 2*mc 1413*mc 1813*mc 1875) + 4096*(mc 1414 + mc 1876 - mc 1814*mc 1876 - 2*mc 1414*mc 1876 + 2*mc 1414*mc 1814*mc 1876) + 8192*(mc 1415 + mc 1877 - mc 1815*mc 1877 - 2*mc 1415*mc 1877 + 2*mc 1415*mc 1815*mc 1877) + 16384*(mc 1416 + mc 1878 - mc 1816*mc 1878 - 2*mc 1416*mc 1878 + 2*mc 1416*mc 1816*mc 1878) + 32768*(mc 1417 + mc 1879 - mc 1817*mc 1879 - 2*mc 1417*mc 1879 + 2*mc 1417*mc 1817*mc 1879)) - mc 2550 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2995, KeccakfPermAir.extraction.inter_6405, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6404 c row = (mc 1403 + mc 1865 - mc 1803*mc 1865 - 2*mc 1403*mc 1865 + 2*mc 1403*mc 1803*mc 1865) + 2 * KeccakfPermAir.extraction.inter_6402 c row := by
    simp only [KeccakfPermAir.extraction.inter_6404, KeccakfPermAir.extraction.inter_6403, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6402 c row = (mc 1404 + mc 1866 - mc 1804*mc 1866 - 2*mc 1404*mc 1866 + 2*mc 1404*mc 1804*mc 1866) + 2 * KeccakfPermAir.extraction.inter_6400 c row := by
    simp only [KeccakfPermAir.extraction.inter_6402, KeccakfPermAir.extraction.inter_6401, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6400 c row = (mc 1405 + mc 1867 - mc 1805*mc 1867 - 2*mc 1405*mc 1867 + 2*mc 1405*mc 1805*mc 1867) + 2 * KeccakfPermAir.extraction.inter_6398 c row := by
    simp only [KeccakfPermAir.extraction.inter_6400, KeccakfPermAir.extraction.inter_6399, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6398 c row = (mc 1406 + mc 1868 - mc 1806*mc 1868 - 2*mc 1406*mc 1868 + 2*mc 1406*mc 1806*mc 1868) + 2 * KeccakfPermAir.extraction.inter_6396 c row := by
    simp only [KeccakfPermAir.extraction.inter_6398, KeccakfPermAir.extraction.inter_6397, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6396 c row = (mc 1407 + mc 1869 - mc 1807*mc 1869 - 2*mc 1407*mc 1869 + 2*mc 1407*mc 1807*mc 1869) + 2 * KeccakfPermAir.extraction.inter_6394 c row := by
    simp only [KeccakfPermAir.extraction.inter_6396, KeccakfPermAir.extraction.inter_6395, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6394 c row = (mc 1408 + mc 1870 - mc 1808*mc 1870 - 2*mc 1408*mc 1870 + 2*mc 1408*mc 1808*mc 1870) + 2 * KeccakfPermAir.extraction.inter_6392 c row := by
    simp only [KeccakfPermAir.extraction.inter_6394, KeccakfPermAir.extraction.inter_6393, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6392 c row = (mc 1409 + mc 1871 - mc 1809*mc 1871 - 2*mc 1409*mc 1871 + 2*mc 1409*mc 1809*mc 1871) + 2 * KeccakfPermAir.extraction.inter_6390 c row := by
    simp only [KeccakfPermAir.extraction.inter_6392, KeccakfPermAir.extraction.inter_6391, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6390 c row = (mc 1410 + mc 1872 - mc 1810*mc 1872 - 2*mc 1410*mc 1872 + 2*mc 1410*mc 1810*mc 1872) + 2 * KeccakfPermAir.extraction.inter_6388 c row := by
    simp only [KeccakfPermAir.extraction.inter_6390, KeccakfPermAir.extraction.inter_6389, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6388 c row = (mc 1411 + mc 1873 - mc 1811*mc 1873 - 2*mc 1411*mc 1873 + 2*mc 1411*mc 1811*mc 1873) + 2 * KeccakfPermAir.extraction.inter_6386 c row := by
    simp only [KeccakfPermAir.extraction.inter_6388, KeccakfPermAir.extraction.inter_6387, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6386 c row = (mc 1412 + mc 1874 - mc 1812*mc 1874 - 2*mc 1412*mc 1874 + 2*mc 1412*mc 1812*mc 1874) + 2 * KeccakfPermAir.extraction.inter_6384 c row := by
    simp only [KeccakfPermAir.extraction.inter_6386, KeccakfPermAir.extraction.inter_6385, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6384 c row = (mc 1413 + mc 1875 - mc 1813*mc 1875 - 2*mc 1413*mc 1875 + 2*mc 1413*mc 1813*mc 1875) + 2 * KeccakfPermAir.extraction.inter_6382 c row := by
    simp only [KeccakfPermAir.extraction.inter_6384, KeccakfPermAir.extraction.inter_6383, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6382 c row = (mc 1414 + mc 1876 - mc 1814*mc 1876 - 2*mc 1414*mc 1876 + 2*mc 1414*mc 1814*mc 1876) + 2 * KeccakfPermAir.extraction.inter_6380 c row := by
    simp only [KeccakfPermAir.extraction.inter_6382, KeccakfPermAir.extraction.inter_6381, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6380 c row = (mc 1415 + mc 1877 - mc 1815*mc 1877 - 2*mc 1415*mc 1877 + 2*mc 1415*mc 1815*mc 1877) + 2 * KeccakfPermAir.extraction.inter_6378 c row := by
    simp only [KeccakfPermAir.extraction.inter_6380, KeccakfPermAir.extraction.inter_6379, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6378 c row = (mc 1416 + mc 1878 - mc 1816*mc 1878 - 2*mc 1416*mc 1878 + 2*mc 1416*mc 1816*mc 1878) + 2 * KeccakfPermAir.extraction.inter_6376 c row := by
    simp only [KeccakfPermAir.extraction.inter_6378, KeccakfPermAir.extraction.inter_6377, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6376 c row = (mc 1417 + mc 1879 - mc 1817*mc 1879 - 2*mc 1417*mc 1879 + 2*mc 1417*mc 1817*mc 1879) := by
    simp only [KeccakfPermAir.extraction.inter_6376, KeccakfPermAir.extraction.inter_6375, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2996 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2996 c row) :
    ((mc 1418 + mc 1880 - mc 1818*mc 1880 - 2*mc 1418*mc 1880 + 2*mc 1418*mc 1818*mc 1880) + 2*(mc 1419 + mc 1881 - mc 1819*mc 1881 - 2*mc 1419*mc 1881 + 2*mc 1419*mc 1819*mc 1881) + 4*(mc 1420 + mc 1882 - mc 1820*mc 1882 - 2*mc 1420*mc 1882 + 2*mc 1420*mc 1820*mc 1882) + 8*(mc 1421 + mc 1883 - mc 1821*mc 1883 - 2*mc 1421*mc 1883 + 2*mc 1421*mc 1821*mc 1883) + 16*(mc 1422 + mc 1884 - mc 1822*mc 1884 - 2*mc 1422*mc 1884 + 2*mc 1422*mc 1822*mc 1884) + 32*(mc 1423 + mc 1885 - mc 1823*mc 1885 - 2*mc 1423*mc 1885 + 2*mc 1423*mc 1823*mc 1885) + 64*(mc 1424 + mc 1886 - mc 1824*mc 1886 - 2*mc 1424*mc 1886 + 2*mc 1424*mc 1824*mc 1886) + 128*(mc 1425 + mc 1887 - mc 1761*mc 1887 - 2*mc 1425*mc 1887 + 2*mc 1425*mc 1761*mc 1887) + 256*(mc 1426 + mc 1888 - mc 1762*mc 1888 - 2*mc 1426*mc 1888 + 2*mc 1426*mc 1762*mc 1888) + 512*(mc 1427 + mc 1825 - mc 1763*mc 1825 - 2*mc 1427*mc 1825 + 2*mc 1427*mc 1763*mc 1825) + 1024*(mc 1428 + mc 1826 - mc 1764*mc 1826 - 2*mc 1428*mc 1826 + 2*mc 1428*mc 1764*mc 1826) + 2048*(mc 1429 + mc 1827 - mc 1765*mc 1827 - 2*mc 1429*mc 1827 + 2*mc 1429*mc 1765*mc 1827) + 4096*(mc 1430 + mc 1828 - mc 1766*mc 1828 - 2*mc 1430*mc 1828 + 2*mc 1430*mc 1766*mc 1828) + 8192*(mc 1431 + mc 1829 - mc 1767*mc 1829 - 2*mc 1431*mc 1829 + 2*mc 1431*mc 1767*mc 1829) + 16384*(mc 1432 + mc 1830 - mc 1768*mc 1830 - 2*mc 1432*mc 1830 + 2*mc 1432*mc 1768*mc 1830) + 32768*(mc 1433 + mc 1831 - mc 1769*mc 1831 - 2*mc 1433*mc 1831 + 2*mc 1433*mc 1769*mc 1831)) - mc 2551 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2996, KeccakfPermAir.extraction.inter_6436, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6435 c row = (mc 1419 + mc 1881 - mc 1819*mc 1881 - 2*mc 1419*mc 1881 + 2*mc 1419*mc 1819*mc 1881) + 2 * KeccakfPermAir.extraction.inter_6433 c row := by
    simp only [KeccakfPermAir.extraction.inter_6435, KeccakfPermAir.extraction.inter_6434, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6433 c row = (mc 1420 + mc 1882 - mc 1820*mc 1882 - 2*mc 1420*mc 1882 + 2*mc 1420*mc 1820*mc 1882) + 2 * KeccakfPermAir.extraction.inter_6431 c row := by
    simp only [KeccakfPermAir.extraction.inter_6433, KeccakfPermAir.extraction.inter_6432, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6431 c row = (mc 1421 + mc 1883 - mc 1821*mc 1883 - 2*mc 1421*mc 1883 + 2*mc 1421*mc 1821*mc 1883) + 2 * KeccakfPermAir.extraction.inter_6429 c row := by
    simp only [KeccakfPermAir.extraction.inter_6431, KeccakfPermAir.extraction.inter_6430, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6429 c row = (mc 1422 + mc 1884 - mc 1822*mc 1884 - 2*mc 1422*mc 1884 + 2*mc 1422*mc 1822*mc 1884) + 2 * KeccakfPermAir.extraction.inter_6427 c row := by
    simp only [KeccakfPermAir.extraction.inter_6429, KeccakfPermAir.extraction.inter_6428, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6427 c row = (mc 1423 + mc 1885 - mc 1823*mc 1885 - 2*mc 1423*mc 1885 + 2*mc 1423*mc 1823*mc 1885) + 2 * KeccakfPermAir.extraction.inter_6425 c row := by
    simp only [KeccakfPermAir.extraction.inter_6427, KeccakfPermAir.extraction.inter_6426, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6425 c row = (mc 1424 + mc 1886 - mc 1824*mc 1886 - 2*mc 1424*mc 1886 + 2*mc 1424*mc 1824*mc 1886) + 2 * KeccakfPermAir.extraction.inter_6423 c row := by
    simp only [KeccakfPermAir.extraction.inter_6425, KeccakfPermAir.extraction.inter_6424, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6423 c row = (mc 1425 + mc 1887 - mc 1761*mc 1887 - 2*mc 1425*mc 1887 + 2*mc 1425*mc 1761*mc 1887) + 2 * KeccakfPermAir.extraction.inter_6421 c row := by
    simp only [KeccakfPermAir.extraction.inter_6423, KeccakfPermAir.extraction.inter_6422, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6421 c row = (mc 1426 + mc 1888 - mc 1762*mc 1888 - 2*mc 1426*mc 1888 + 2*mc 1426*mc 1762*mc 1888) + 2 * KeccakfPermAir.extraction.inter_6419 c row := by
    simp only [KeccakfPermAir.extraction.inter_6421, KeccakfPermAir.extraction.inter_6420, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6419 c row = (mc 1427 + mc 1825 - mc 1763*mc 1825 - 2*mc 1427*mc 1825 + 2*mc 1427*mc 1763*mc 1825) + 2 * KeccakfPermAir.extraction.inter_6417 c row := by
    simp only [KeccakfPermAir.extraction.inter_6419, KeccakfPermAir.extraction.inter_6418, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6417 c row = (mc 1428 + mc 1826 - mc 1764*mc 1826 - 2*mc 1428*mc 1826 + 2*mc 1428*mc 1764*mc 1826) + 2 * KeccakfPermAir.extraction.inter_6415 c row := by
    simp only [KeccakfPermAir.extraction.inter_6417, KeccakfPermAir.extraction.inter_6416, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6415 c row = (mc 1429 + mc 1827 - mc 1765*mc 1827 - 2*mc 1429*mc 1827 + 2*mc 1429*mc 1765*mc 1827) + 2 * KeccakfPermAir.extraction.inter_6413 c row := by
    simp only [KeccakfPermAir.extraction.inter_6415, KeccakfPermAir.extraction.inter_6414, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6413 c row = (mc 1430 + mc 1828 - mc 1766*mc 1828 - 2*mc 1430*mc 1828 + 2*mc 1430*mc 1766*mc 1828) + 2 * KeccakfPermAir.extraction.inter_6411 c row := by
    simp only [KeccakfPermAir.extraction.inter_6413, KeccakfPermAir.extraction.inter_6412, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6411 c row = (mc 1431 + mc 1829 - mc 1767*mc 1829 - 2*mc 1431*mc 1829 + 2*mc 1431*mc 1767*mc 1829) + 2 * KeccakfPermAir.extraction.inter_6409 c row := by
    simp only [KeccakfPermAir.extraction.inter_6411, KeccakfPermAir.extraction.inter_6410, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6409 c row = (mc 1432 + mc 1830 - mc 1768*mc 1830 - 2*mc 1432*mc 1830 + 2*mc 1432*mc 1768*mc 1830) + 2 * KeccakfPermAir.extraction.inter_6407 c row := by
    simp only [KeccakfPermAir.extraction.inter_6409, KeccakfPermAir.extraction.inter_6408, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6407 c row = (mc 1433 + mc 1831 - mc 1769*mc 1831 - 2*mc 1433*mc 1831 + 2*mc 1433*mc 1769*mc 1831) := by
    simp only [KeccakfPermAir.extraction.inter_6407, KeccakfPermAir.extraction.inter_6406, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2997 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2997 c row) :
    ((mc 1434 + mc 1832 - mc 1770*mc 1832 - 2*mc 1434*mc 1832 + 2*mc 1434*mc 1770*mc 1832) + 2*(mc 1435 + mc 1833 - mc 1771*mc 1833 - 2*mc 1435*mc 1833 + 2*mc 1435*mc 1771*mc 1833) + 4*(mc 1436 + mc 1834 - mc 1772*mc 1834 - 2*mc 1436*mc 1834 + 2*mc 1436*mc 1772*mc 1834) + 8*(mc 1437 + mc 1835 - mc 1773*mc 1835 - 2*mc 1437*mc 1835 + 2*mc 1437*mc 1773*mc 1835) + 16*(mc 1438 + mc 1836 - mc 1774*mc 1836 - 2*mc 1438*mc 1836 + 2*mc 1438*mc 1774*mc 1836) + 32*(mc 1439 + mc 1837 - mc 1775*mc 1837 - 2*mc 1439*mc 1837 + 2*mc 1439*mc 1775*mc 1837) + 64*(mc 1440 + mc 1838 - mc 1776*mc 1838 - 2*mc 1440*mc 1838 + 2*mc 1440*mc 1776*mc 1838) + 128*(mc 1377 + mc 1839 - mc 1777*mc 1839 - 2*mc 1377*mc 1839 + 2*mc 1377*mc 1777*mc 1839) + 256*(mc 1378 + mc 1840 - mc 1778*mc 1840 - 2*mc 1378*mc 1840 + 2*mc 1378*mc 1778*mc 1840) + 512*(mc 1379 + mc 1841 - mc 1779*mc 1841 - 2*mc 1379*mc 1841 + 2*mc 1379*mc 1779*mc 1841) + 1024*(mc 1380 + mc 1842 - mc 1780*mc 1842 - 2*mc 1380*mc 1842 + 2*mc 1380*mc 1780*mc 1842) + 2048*(mc 1381 + mc 1843 - mc 1781*mc 1843 - 2*mc 1381*mc 1843 + 2*mc 1381*mc 1781*mc 1843) + 4096*(mc 1382 + mc 1844 - mc 1782*mc 1844 - 2*mc 1382*mc 1844 + 2*mc 1382*mc 1782*mc 1844) + 8192*(mc 1383 + mc 1845 - mc 1783*mc 1845 - 2*mc 1383*mc 1845 + 2*mc 1383*mc 1783*mc 1845) + 16384*(mc 1384 + mc 1846 - mc 1784*mc 1846 - 2*mc 1384*mc 1846 + 2*mc 1384*mc 1784*mc 1846) + 32768*(mc 1385 + mc 1847 - mc 1785*mc 1847 - 2*mc 1385*mc 1847 + 2*mc 1385*mc 1785*mc 1847)) - mc 2552 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2997, KeccakfPermAir.extraction.inter_6467, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6466 c row = (mc 1435 + mc 1833 - mc 1771*mc 1833 - 2*mc 1435*mc 1833 + 2*mc 1435*mc 1771*mc 1833) + 2 * KeccakfPermAir.extraction.inter_6464 c row := by
    simp only [KeccakfPermAir.extraction.inter_6466, KeccakfPermAir.extraction.inter_6465, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6464 c row = (mc 1436 + mc 1834 - mc 1772*mc 1834 - 2*mc 1436*mc 1834 + 2*mc 1436*mc 1772*mc 1834) + 2 * KeccakfPermAir.extraction.inter_6462 c row := by
    simp only [KeccakfPermAir.extraction.inter_6464, KeccakfPermAir.extraction.inter_6463, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6462 c row = (mc 1437 + mc 1835 - mc 1773*mc 1835 - 2*mc 1437*mc 1835 + 2*mc 1437*mc 1773*mc 1835) + 2 * KeccakfPermAir.extraction.inter_6460 c row := by
    simp only [KeccakfPermAir.extraction.inter_6462, KeccakfPermAir.extraction.inter_6461, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6460 c row = (mc 1438 + mc 1836 - mc 1774*mc 1836 - 2*mc 1438*mc 1836 + 2*mc 1438*mc 1774*mc 1836) + 2 * KeccakfPermAir.extraction.inter_6458 c row := by
    simp only [KeccakfPermAir.extraction.inter_6460, KeccakfPermAir.extraction.inter_6459, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6458 c row = (mc 1439 + mc 1837 - mc 1775*mc 1837 - 2*mc 1439*mc 1837 + 2*mc 1439*mc 1775*mc 1837) + 2 * KeccakfPermAir.extraction.inter_6456 c row := by
    simp only [KeccakfPermAir.extraction.inter_6458, KeccakfPermAir.extraction.inter_6457, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6456 c row = (mc 1440 + mc 1838 - mc 1776*mc 1838 - 2*mc 1440*mc 1838 + 2*mc 1440*mc 1776*mc 1838) + 2 * KeccakfPermAir.extraction.inter_6454 c row := by
    simp only [KeccakfPermAir.extraction.inter_6456, KeccakfPermAir.extraction.inter_6455, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6454 c row = (mc 1377 + mc 1839 - mc 1777*mc 1839 - 2*mc 1377*mc 1839 + 2*mc 1377*mc 1777*mc 1839) + 2 * KeccakfPermAir.extraction.inter_6452 c row := by
    simp only [KeccakfPermAir.extraction.inter_6454, KeccakfPermAir.extraction.inter_6453, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6452 c row = (mc 1378 + mc 1840 - mc 1778*mc 1840 - 2*mc 1378*mc 1840 + 2*mc 1378*mc 1778*mc 1840) + 2 * KeccakfPermAir.extraction.inter_6450 c row := by
    simp only [KeccakfPermAir.extraction.inter_6452, KeccakfPermAir.extraction.inter_6451, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6450 c row = (mc 1379 + mc 1841 - mc 1779*mc 1841 - 2*mc 1379*mc 1841 + 2*mc 1379*mc 1779*mc 1841) + 2 * KeccakfPermAir.extraction.inter_6448 c row := by
    simp only [KeccakfPermAir.extraction.inter_6450, KeccakfPermAir.extraction.inter_6449, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6448 c row = (mc 1380 + mc 1842 - mc 1780*mc 1842 - 2*mc 1380*mc 1842 + 2*mc 1380*mc 1780*mc 1842) + 2 * KeccakfPermAir.extraction.inter_6446 c row := by
    simp only [KeccakfPermAir.extraction.inter_6448, KeccakfPermAir.extraction.inter_6447, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6446 c row = (mc 1381 + mc 1843 - mc 1781*mc 1843 - 2*mc 1381*mc 1843 + 2*mc 1381*mc 1781*mc 1843) + 2 * KeccakfPermAir.extraction.inter_6444 c row := by
    simp only [KeccakfPermAir.extraction.inter_6446, KeccakfPermAir.extraction.inter_6445, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6444 c row = (mc 1382 + mc 1844 - mc 1782*mc 1844 - 2*mc 1382*mc 1844 + 2*mc 1382*mc 1782*mc 1844) + 2 * KeccakfPermAir.extraction.inter_6442 c row := by
    simp only [KeccakfPermAir.extraction.inter_6444, KeccakfPermAir.extraction.inter_6443, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6442 c row = (mc 1383 + mc 1845 - mc 1783*mc 1845 - 2*mc 1383*mc 1845 + 2*mc 1383*mc 1783*mc 1845) + 2 * KeccakfPermAir.extraction.inter_6440 c row := by
    simp only [KeccakfPermAir.extraction.inter_6442, KeccakfPermAir.extraction.inter_6441, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6440 c row = (mc 1384 + mc 1846 - mc 1784*mc 1846 - 2*mc 1384*mc 1846 + 2*mc 1384*mc 1784*mc 1846) + 2 * KeccakfPermAir.extraction.inter_6438 c row := by
    simp only [KeccakfPermAir.extraction.inter_6440, KeccakfPermAir.extraction.inter_6439, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6438 c row = (mc 1385 + mc 1847 - mc 1785*mc 1847 - 2*mc 1385*mc 1847 + 2*mc 1385*mc 1785*mc 1847) := by
    simp only [KeccakfPermAir.extraction.inter_6438, KeccakfPermAir.extraction.inter_6437, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2998 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2998 c row) :
    ((mc 1786 + mc 2271 - mc 1848*mc 2271 - 2*mc 1786*mc 2271 + 2*mc 1786*mc 1848*mc 2271) + 2*(mc 1787 + mc 2272 - mc 1849*mc 2272 - 2*mc 1787*mc 2272 + 2*mc 1787*mc 1849*mc 2272) + 4*(mc 1788 + mc 2209 - mc 1850*mc 2209 - 2*mc 1788*mc 2209 + 2*mc 1788*mc 1850*mc 2209) + 8*(mc 1789 + mc 2210 - mc 1851*mc 2210 - 2*mc 1789*mc 2210 + 2*mc 1789*mc 1851*mc 2210) + 16*(mc 1790 + mc 2211 - mc 1852*mc 2211 - 2*mc 1790*mc 2211 + 2*mc 1790*mc 1852*mc 2211) + 32*(mc 1791 + mc 2212 - mc 1853*mc 2212 - 2*mc 1791*mc 2212 + 2*mc 1791*mc 1853*mc 2212) + 64*(mc 1792 + mc 2213 - mc 1854*mc 2213 - 2*mc 1792*mc 2213 + 2*mc 1792*mc 1854*mc 2213) + 128*(mc 1793 + mc 2214 - mc 1855*mc 2214 - 2*mc 1793*mc 2214 + 2*mc 1793*mc 1855*mc 2214) + 256*(mc 1794 + mc 2215 - mc 1856*mc 2215 - 2*mc 1794*mc 2215 + 2*mc 1794*mc 1856*mc 2215) + 512*(mc 1795 + mc 2216 - mc 1857*mc 2216 - 2*mc 1795*mc 2216 + 2*mc 1795*mc 1857*mc 2216) + 1024*(mc 1796 + mc 2217 - mc 1858*mc 2217 - 2*mc 1796*mc 2217 + 2*mc 1796*mc 1858*mc 2217) + 2048*(mc 1797 + mc 2218 - mc 1859*mc 2218 - 2*mc 1797*mc 2218 + 2*mc 1797*mc 1859*mc 2218) + 4096*(mc 1798 + mc 2219 - mc 1860*mc 2219 - 2*mc 1798*mc 2219 + 2*mc 1798*mc 1860*mc 2219) + 8192*(mc 1799 + mc 2220 - mc 1861*mc 2220 - 2*mc 1799*mc 2220 + 2*mc 1799*mc 1861*mc 2220) + 16384*(mc 1800 + mc 2221 - mc 1862*mc 2221 - 2*mc 1800*mc 2221 + 2*mc 1800*mc 1862*mc 2221) + 32768*(mc 1801 + mc 2222 - mc 1863*mc 2222 - 2*mc 1801*mc 2222 + 2*mc 1801*mc 1863*mc 2222)) - mc 2553 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2998, KeccakfPermAir.extraction.inter_6498, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6497 c row = (mc 1787 + mc 2272 - mc 1849*mc 2272 - 2*mc 1787*mc 2272 + 2*mc 1787*mc 1849*mc 2272) + 2 * KeccakfPermAir.extraction.inter_6495 c row := by
    simp only [KeccakfPermAir.extraction.inter_6497, KeccakfPermAir.extraction.inter_6496, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6495 c row = (mc 1788 + mc 2209 - mc 1850*mc 2209 - 2*mc 1788*mc 2209 + 2*mc 1788*mc 1850*mc 2209) + 2 * KeccakfPermAir.extraction.inter_6493 c row := by
    simp only [KeccakfPermAir.extraction.inter_6495, KeccakfPermAir.extraction.inter_6494, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6493 c row = (mc 1789 + mc 2210 - mc 1851*mc 2210 - 2*mc 1789*mc 2210 + 2*mc 1789*mc 1851*mc 2210) + 2 * KeccakfPermAir.extraction.inter_6491 c row := by
    simp only [KeccakfPermAir.extraction.inter_6493, KeccakfPermAir.extraction.inter_6492, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6491 c row = (mc 1790 + mc 2211 - mc 1852*mc 2211 - 2*mc 1790*mc 2211 + 2*mc 1790*mc 1852*mc 2211) + 2 * KeccakfPermAir.extraction.inter_6489 c row := by
    simp only [KeccakfPermAir.extraction.inter_6491, KeccakfPermAir.extraction.inter_6490, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6489 c row = (mc 1791 + mc 2212 - mc 1853*mc 2212 - 2*mc 1791*mc 2212 + 2*mc 1791*mc 1853*mc 2212) + 2 * KeccakfPermAir.extraction.inter_6487 c row := by
    simp only [KeccakfPermAir.extraction.inter_6489, KeccakfPermAir.extraction.inter_6488, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6487 c row = (mc 1792 + mc 2213 - mc 1854*mc 2213 - 2*mc 1792*mc 2213 + 2*mc 1792*mc 1854*mc 2213) + 2 * KeccakfPermAir.extraction.inter_6485 c row := by
    simp only [KeccakfPermAir.extraction.inter_6487, KeccakfPermAir.extraction.inter_6486, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6485 c row = (mc 1793 + mc 2214 - mc 1855*mc 2214 - 2*mc 1793*mc 2214 + 2*mc 1793*mc 1855*mc 2214) + 2 * KeccakfPermAir.extraction.inter_6483 c row := by
    simp only [KeccakfPermAir.extraction.inter_6485, KeccakfPermAir.extraction.inter_6484, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6483 c row = (mc 1794 + mc 2215 - mc 1856*mc 2215 - 2*mc 1794*mc 2215 + 2*mc 1794*mc 1856*mc 2215) + 2 * KeccakfPermAir.extraction.inter_6481 c row := by
    simp only [KeccakfPermAir.extraction.inter_6483, KeccakfPermAir.extraction.inter_6482, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6481 c row = (mc 1795 + mc 2216 - mc 1857*mc 2216 - 2*mc 1795*mc 2216 + 2*mc 1795*mc 1857*mc 2216) + 2 * KeccakfPermAir.extraction.inter_6479 c row := by
    simp only [KeccakfPermAir.extraction.inter_6481, KeccakfPermAir.extraction.inter_6480, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6479 c row = (mc 1796 + mc 2217 - mc 1858*mc 2217 - 2*mc 1796*mc 2217 + 2*mc 1796*mc 1858*mc 2217) + 2 * KeccakfPermAir.extraction.inter_6477 c row := by
    simp only [KeccakfPermAir.extraction.inter_6479, KeccakfPermAir.extraction.inter_6478, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6477 c row = (mc 1797 + mc 2218 - mc 1859*mc 2218 - 2*mc 1797*mc 2218 + 2*mc 1797*mc 1859*mc 2218) + 2 * KeccakfPermAir.extraction.inter_6475 c row := by
    simp only [KeccakfPermAir.extraction.inter_6477, KeccakfPermAir.extraction.inter_6476, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6475 c row = (mc 1798 + mc 2219 - mc 1860*mc 2219 - 2*mc 1798*mc 2219 + 2*mc 1798*mc 1860*mc 2219) + 2 * KeccakfPermAir.extraction.inter_6473 c row := by
    simp only [KeccakfPermAir.extraction.inter_6475, KeccakfPermAir.extraction.inter_6474, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6473 c row = (mc 1799 + mc 2220 - mc 1861*mc 2220 - 2*mc 1799*mc 2220 + 2*mc 1799*mc 1861*mc 2220) + 2 * KeccakfPermAir.extraction.inter_6471 c row := by
    simp only [KeccakfPermAir.extraction.inter_6473, KeccakfPermAir.extraction.inter_6472, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6471 c row = (mc 1800 + mc 2221 - mc 1862*mc 2221 - 2*mc 1800*mc 2221 + 2*mc 1800*mc 1862*mc 2221) + 2 * KeccakfPermAir.extraction.inter_6469 c row := by
    simp only [KeccakfPermAir.extraction.inter_6471, KeccakfPermAir.extraction.inter_6470, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6469 c row = (mc 1801 + mc 2222 - mc 1863*mc 2222 - 2*mc 1801*mc 2222 + 2*mc 1801*mc 1863*mc 2222) := by
    simp only [KeccakfPermAir.extraction.inter_6469, KeccakfPermAir.extraction.inter_6468, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_2999 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_2999 c row) :
    ((mc 1802 + mc 2223 - mc 1864*mc 2223 - 2*mc 1802*mc 2223 + 2*mc 1802*mc 1864*mc 2223) + 2*(mc 1803 + mc 2224 - mc 1865*mc 2224 - 2*mc 1803*mc 2224 + 2*mc 1803*mc 1865*mc 2224) + 4*(mc 1804 + mc 2225 - mc 1866*mc 2225 - 2*mc 1804*mc 2225 + 2*mc 1804*mc 1866*mc 2225) + 8*(mc 1805 + mc 2226 - mc 1867*mc 2226 - 2*mc 1805*mc 2226 + 2*mc 1805*mc 1867*mc 2226) + 16*(mc 1806 + mc 2227 - mc 1868*mc 2227 - 2*mc 1806*mc 2227 + 2*mc 1806*mc 1868*mc 2227) + 32*(mc 1807 + mc 2228 - mc 1869*mc 2228 - 2*mc 1807*mc 2228 + 2*mc 1807*mc 1869*mc 2228) + 64*(mc 1808 + mc 2229 - mc 1870*mc 2229 - 2*mc 1808*mc 2229 + 2*mc 1808*mc 1870*mc 2229) + 128*(mc 1809 + mc 2230 - mc 1871*mc 2230 - 2*mc 1809*mc 2230 + 2*mc 1809*mc 1871*mc 2230) + 256*(mc 1810 + mc 2231 - mc 1872*mc 2231 - 2*mc 1810*mc 2231 + 2*mc 1810*mc 1872*mc 2231) + 512*(mc 1811 + mc 2232 - mc 1873*mc 2232 - 2*mc 1811*mc 2232 + 2*mc 1811*mc 1873*mc 2232) + 1024*(mc 1812 + mc 2233 - mc 1874*mc 2233 - 2*mc 1812*mc 2233 + 2*mc 1812*mc 1874*mc 2233) + 2048*(mc 1813 + mc 2234 - mc 1875*mc 2234 - 2*mc 1813*mc 2234 + 2*mc 1813*mc 1875*mc 2234) + 4096*(mc 1814 + mc 2235 - mc 1876*mc 2235 - 2*mc 1814*mc 2235 + 2*mc 1814*mc 1876*mc 2235) + 8192*(mc 1815 + mc 2236 - mc 1877*mc 2236 - 2*mc 1815*mc 2236 + 2*mc 1815*mc 1877*mc 2236) + 16384*(mc 1816 + mc 2237 - mc 1878*mc 2237 - 2*mc 1816*mc 2237 + 2*mc 1816*mc 1878*mc 2237) + 32768*(mc 1817 + mc 2238 - mc 1879*mc 2238 - 2*mc 1817*mc 2238 + 2*mc 1817*mc 1879*mc 2238)) - mc 2554 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_2999, KeccakfPermAir.extraction.inter_6529, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6528 c row = (mc 1803 + mc 2224 - mc 1865*mc 2224 - 2*mc 1803*mc 2224 + 2*mc 1803*mc 1865*mc 2224) + 2 * KeccakfPermAir.extraction.inter_6526 c row := by
    simp only [KeccakfPermAir.extraction.inter_6528, KeccakfPermAir.extraction.inter_6527, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6526 c row = (mc 1804 + mc 2225 - mc 1866*mc 2225 - 2*mc 1804*mc 2225 + 2*mc 1804*mc 1866*mc 2225) + 2 * KeccakfPermAir.extraction.inter_6524 c row := by
    simp only [KeccakfPermAir.extraction.inter_6526, KeccakfPermAir.extraction.inter_6525, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6524 c row = (mc 1805 + mc 2226 - mc 1867*mc 2226 - 2*mc 1805*mc 2226 + 2*mc 1805*mc 1867*mc 2226) + 2 * KeccakfPermAir.extraction.inter_6522 c row := by
    simp only [KeccakfPermAir.extraction.inter_6524, KeccakfPermAir.extraction.inter_6523, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6522 c row = (mc 1806 + mc 2227 - mc 1868*mc 2227 - 2*mc 1806*mc 2227 + 2*mc 1806*mc 1868*mc 2227) + 2 * KeccakfPermAir.extraction.inter_6520 c row := by
    simp only [KeccakfPermAir.extraction.inter_6522, KeccakfPermAir.extraction.inter_6521, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6520 c row = (mc 1807 + mc 2228 - mc 1869*mc 2228 - 2*mc 1807*mc 2228 + 2*mc 1807*mc 1869*mc 2228) + 2 * KeccakfPermAir.extraction.inter_6518 c row := by
    simp only [KeccakfPermAir.extraction.inter_6520, KeccakfPermAir.extraction.inter_6519, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6518 c row = (mc 1808 + mc 2229 - mc 1870*mc 2229 - 2*mc 1808*mc 2229 + 2*mc 1808*mc 1870*mc 2229) + 2 * KeccakfPermAir.extraction.inter_6516 c row := by
    simp only [KeccakfPermAir.extraction.inter_6518, KeccakfPermAir.extraction.inter_6517, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6516 c row = (mc 1809 + mc 2230 - mc 1871*mc 2230 - 2*mc 1809*mc 2230 + 2*mc 1809*mc 1871*mc 2230) + 2 * KeccakfPermAir.extraction.inter_6514 c row := by
    simp only [KeccakfPermAir.extraction.inter_6516, KeccakfPermAir.extraction.inter_6515, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6514 c row = (mc 1810 + mc 2231 - mc 1872*mc 2231 - 2*mc 1810*mc 2231 + 2*mc 1810*mc 1872*mc 2231) + 2 * KeccakfPermAir.extraction.inter_6512 c row := by
    simp only [KeccakfPermAir.extraction.inter_6514, KeccakfPermAir.extraction.inter_6513, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6512 c row = (mc 1811 + mc 2232 - mc 1873*mc 2232 - 2*mc 1811*mc 2232 + 2*mc 1811*mc 1873*mc 2232) + 2 * KeccakfPermAir.extraction.inter_6510 c row := by
    simp only [KeccakfPermAir.extraction.inter_6512, KeccakfPermAir.extraction.inter_6511, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6510 c row = (mc 1812 + mc 2233 - mc 1874*mc 2233 - 2*mc 1812*mc 2233 + 2*mc 1812*mc 1874*mc 2233) + 2 * KeccakfPermAir.extraction.inter_6508 c row := by
    simp only [KeccakfPermAir.extraction.inter_6510, KeccakfPermAir.extraction.inter_6509, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6508 c row = (mc 1813 + mc 2234 - mc 1875*mc 2234 - 2*mc 1813*mc 2234 + 2*mc 1813*mc 1875*mc 2234) + 2 * KeccakfPermAir.extraction.inter_6506 c row := by
    simp only [KeccakfPermAir.extraction.inter_6508, KeccakfPermAir.extraction.inter_6507, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6506 c row = (mc 1814 + mc 2235 - mc 1876*mc 2235 - 2*mc 1814*mc 2235 + 2*mc 1814*mc 1876*mc 2235) + 2 * KeccakfPermAir.extraction.inter_6504 c row := by
    simp only [KeccakfPermAir.extraction.inter_6506, KeccakfPermAir.extraction.inter_6505, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6504 c row = (mc 1815 + mc 2236 - mc 1877*mc 2236 - 2*mc 1815*mc 2236 + 2*mc 1815*mc 1877*mc 2236) + 2 * KeccakfPermAir.extraction.inter_6502 c row := by
    simp only [KeccakfPermAir.extraction.inter_6504, KeccakfPermAir.extraction.inter_6503, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6502 c row = (mc 1816 + mc 2237 - mc 1878*mc 2237 - 2*mc 1816*mc 2237 + 2*mc 1816*mc 1878*mc 2237) + 2 * KeccakfPermAir.extraction.inter_6500 c row := by
    simp only [KeccakfPermAir.extraction.inter_6502, KeccakfPermAir.extraction.inter_6501, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6500 c row = (mc 1817 + mc 2238 - mc 1879*mc 2238 - 2*mc 1817*mc 2238 + 2*mc 1817*mc 1879*mc 2238) := by
    simp only [KeccakfPermAir.extraction.inter_6500, KeccakfPermAir.extraction.inter_6499, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_3000 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3000 c row) :
    ((mc 1818 + mc 2239 - mc 1880*mc 2239 - 2*mc 1818*mc 2239 + 2*mc 1818*mc 1880*mc 2239) + 2*(mc 1819 + mc 2240 - mc 1881*mc 2240 - 2*mc 1819*mc 2240 + 2*mc 1819*mc 1881*mc 2240) + 4*(mc 1820 + mc 2241 - mc 1882*mc 2241 - 2*mc 1820*mc 2241 + 2*mc 1820*mc 1882*mc 2241) + 8*(mc 1821 + mc 2242 - mc 1883*mc 2242 - 2*mc 1821*mc 2242 + 2*mc 1821*mc 1883*mc 2242) + 16*(mc 1822 + mc 2243 - mc 1884*mc 2243 - 2*mc 1822*mc 2243 + 2*mc 1822*mc 1884*mc 2243) + 32*(mc 1823 + mc 2244 - mc 1885*mc 2244 - 2*mc 1823*mc 2244 + 2*mc 1823*mc 1885*mc 2244) + 64*(mc 1824 + mc 2245 - mc 1886*mc 2245 - 2*mc 1824*mc 2245 + 2*mc 1824*mc 1886*mc 2245) + 128*(mc 1761 + mc 2246 - mc 1887*mc 2246 - 2*mc 1761*mc 2246 + 2*mc 1761*mc 1887*mc 2246) + 256*(mc 1762 + mc 2247 - mc 1888*mc 2247 - 2*mc 1762*mc 2247 + 2*mc 1762*mc 1888*mc 2247) + 512*(mc 1763 + mc 2248 - mc 1825*mc 2248 - 2*mc 1763*mc 2248 + 2*mc 1763*mc 1825*mc 2248) + 1024*(mc 1764 + mc 2249 - mc 1826*mc 2249 - 2*mc 1764*mc 2249 + 2*mc 1764*mc 1826*mc 2249) + 2048*(mc 1765 + mc 2250 - mc 1827*mc 2250 - 2*mc 1765*mc 2250 + 2*mc 1765*mc 1827*mc 2250) + 4096*(mc 1766 + mc 2251 - mc 1828*mc 2251 - 2*mc 1766*mc 2251 + 2*mc 1766*mc 1828*mc 2251) + 8192*(mc 1767 + mc 2252 - mc 1829*mc 2252 - 2*mc 1767*mc 2252 + 2*mc 1767*mc 1829*mc 2252) + 16384*(mc 1768 + mc 2253 - mc 1830*mc 2253 - 2*mc 1768*mc 2253 + 2*mc 1768*mc 1830*mc 2253) + 32768*(mc 1769 + mc 2254 - mc 1831*mc 2254 - 2*mc 1769*mc 2254 + 2*mc 1769*mc 1831*mc 2254)) - mc 2555 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_3000, KeccakfPermAir.extraction.inter_6560, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6559 c row = (mc 1819 + mc 2240 - mc 1881*mc 2240 - 2*mc 1819*mc 2240 + 2*mc 1819*mc 1881*mc 2240) + 2 * KeccakfPermAir.extraction.inter_6557 c row := by
    simp only [KeccakfPermAir.extraction.inter_6559, KeccakfPermAir.extraction.inter_6558, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6557 c row = (mc 1820 + mc 2241 - mc 1882*mc 2241 - 2*mc 1820*mc 2241 + 2*mc 1820*mc 1882*mc 2241) + 2 * KeccakfPermAir.extraction.inter_6555 c row := by
    simp only [KeccakfPermAir.extraction.inter_6557, KeccakfPermAir.extraction.inter_6556, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6555 c row = (mc 1821 + mc 2242 - mc 1883*mc 2242 - 2*mc 1821*mc 2242 + 2*mc 1821*mc 1883*mc 2242) + 2 * KeccakfPermAir.extraction.inter_6553 c row := by
    simp only [KeccakfPermAir.extraction.inter_6555, KeccakfPermAir.extraction.inter_6554, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6553 c row = (mc 1822 + mc 2243 - mc 1884*mc 2243 - 2*mc 1822*mc 2243 + 2*mc 1822*mc 1884*mc 2243) + 2 * KeccakfPermAir.extraction.inter_6551 c row := by
    simp only [KeccakfPermAir.extraction.inter_6553, KeccakfPermAir.extraction.inter_6552, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6551 c row = (mc 1823 + mc 2244 - mc 1885*mc 2244 - 2*mc 1823*mc 2244 + 2*mc 1823*mc 1885*mc 2244) + 2 * KeccakfPermAir.extraction.inter_6549 c row := by
    simp only [KeccakfPermAir.extraction.inter_6551, KeccakfPermAir.extraction.inter_6550, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6549 c row = (mc 1824 + mc 2245 - mc 1886*mc 2245 - 2*mc 1824*mc 2245 + 2*mc 1824*mc 1886*mc 2245) + 2 * KeccakfPermAir.extraction.inter_6547 c row := by
    simp only [KeccakfPermAir.extraction.inter_6549, KeccakfPermAir.extraction.inter_6548, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6547 c row = (mc 1761 + mc 2246 - mc 1887*mc 2246 - 2*mc 1761*mc 2246 + 2*mc 1761*mc 1887*mc 2246) + 2 * KeccakfPermAir.extraction.inter_6545 c row := by
    simp only [KeccakfPermAir.extraction.inter_6547, KeccakfPermAir.extraction.inter_6546, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6545 c row = (mc 1762 + mc 2247 - mc 1888*mc 2247 - 2*mc 1762*mc 2247 + 2*mc 1762*mc 1888*mc 2247) + 2 * KeccakfPermAir.extraction.inter_6543 c row := by
    simp only [KeccakfPermAir.extraction.inter_6545, KeccakfPermAir.extraction.inter_6544, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6543 c row = (mc 1763 + mc 2248 - mc 1825*mc 2248 - 2*mc 1763*mc 2248 + 2*mc 1763*mc 1825*mc 2248) + 2 * KeccakfPermAir.extraction.inter_6541 c row := by
    simp only [KeccakfPermAir.extraction.inter_6543, KeccakfPermAir.extraction.inter_6542, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6541 c row = (mc 1764 + mc 2249 - mc 1826*mc 2249 - 2*mc 1764*mc 2249 + 2*mc 1764*mc 1826*mc 2249) + 2 * KeccakfPermAir.extraction.inter_6539 c row := by
    simp only [KeccakfPermAir.extraction.inter_6541, KeccakfPermAir.extraction.inter_6540, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6539 c row = (mc 1765 + mc 2250 - mc 1827*mc 2250 - 2*mc 1765*mc 2250 + 2*mc 1765*mc 1827*mc 2250) + 2 * KeccakfPermAir.extraction.inter_6537 c row := by
    simp only [KeccakfPermAir.extraction.inter_6539, KeccakfPermAir.extraction.inter_6538, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6537 c row = (mc 1766 + mc 2251 - mc 1828*mc 2251 - 2*mc 1766*mc 2251 + 2*mc 1766*mc 1828*mc 2251) + 2 * KeccakfPermAir.extraction.inter_6535 c row := by
    simp only [KeccakfPermAir.extraction.inter_6537, KeccakfPermAir.extraction.inter_6536, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6535 c row = (mc 1767 + mc 2252 - mc 1829*mc 2252 - 2*mc 1767*mc 2252 + 2*mc 1767*mc 1829*mc 2252) + 2 * KeccakfPermAir.extraction.inter_6533 c row := by
    simp only [KeccakfPermAir.extraction.inter_6535, KeccakfPermAir.extraction.inter_6534, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6533 c row = (mc 1768 + mc 2253 - mc 1830*mc 2253 - 2*mc 1768*mc 2253 + 2*mc 1768*mc 1830*mc 2253) + 2 * KeccakfPermAir.extraction.inter_6531 c row := by
    simp only [KeccakfPermAir.extraction.inter_6533, KeccakfPermAir.extraction.inter_6532, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6531 c row = (mc 1769 + mc 2254 - mc 1831*mc 2254 - 2*mc 1769*mc 2254 + 2*mc 1769*mc 1831*mc 2254) := by
    simp only [KeccakfPermAir.extraction.inter_6531, KeccakfPermAir.extraction.inter_6530, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_3001 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3001 c row) :
    ((mc 1770 + mc 2255 - mc 1832*mc 2255 - 2*mc 1770*mc 2255 + 2*mc 1770*mc 1832*mc 2255) + 2*(mc 1771 + mc 2256 - mc 1833*mc 2256 - 2*mc 1771*mc 2256 + 2*mc 1771*mc 1833*mc 2256) + 4*(mc 1772 + mc 2257 - mc 1834*mc 2257 - 2*mc 1772*mc 2257 + 2*mc 1772*mc 1834*mc 2257) + 8*(mc 1773 + mc 2258 - mc 1835*mc 2258 - 2*mc 1773*mc 2258 + 2*mc 1773*mc 1835*mc 2258) + 16*(mc 1774 + mc 2259 - mc 1836*mc 2259 - 2*mc 1774*mc 2259 + 2*mc 1774*mc 1836*mc 2259) + 32*(mc 1775 + mc 2260 - mc 1837*mc 2260 - 2*mc 1775*mc 2260 + 2*mc 1775*mc 1837*mc 2260) + 64*(mc 1776 + mc 2261 - mc 1838*mc 2261 - 2*mc 1776*mc 2261 + 2*mc 1776*mc 1838*mc 2261) + 128*(mc 1777 + mc 2262 - mc 1839*mc 2262 - 2*mc 1777*mc 2262 + 2*mc 1777*mc 1839*mc 2262) + 256*(mc 1778 + mc 2263 - mc 1840*mc 2263 - 2*mc 1778*mc 2263 + 2*mc 1778*mc 1840*mc 2263) + 512*(mc 1779 + mc 2264 - mc 1841*mc 2264 - 2*mc 1779*mc 2264 + 2*mc 1779*mc 1841*mc 2264) + 1024*(mc 1780 + mc 2265 - mc 1842*mc 2265 - 2*mc 1780*mc 2265 + 2*mc 1780*mc 1842*mc 2265) + 2048*(mc 1781 + mc 2266 - mc 1843*mc 2266 - 2*mc 1781*mc 2266 + 2*mc 1781*mc 1843*mc 2266) + 4096*(mc 1782 + mc 2267 - mc 1844*mc 2267 - 2*mc 1782*mc 2267 + 2*mc 1782*mc 1844*mc 2267) + 8192*(mc 1783 + mc 2268 - mc 1845*mc 2268 - 2*mc 1783*mc 2268 + 2*mc 1783*mc 1845*mc 2268) + 16384*(mc 1784 + mc 2269 - mc 1846*mc 2269 - 2*mc 1784*mc 2269 + 2*mc 1784*mc 1846*mc 2269) + 32768*(mc 1785 + mc 2270 - mc 1847*mc 2270 - 2*mc 1785*mc 2270 + 2*mc 1785*mc 1847*mc 2270)) - mc 2556 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_3001, KeccakfPermAir.extraction.inter_6591, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6590 c row = (mc 1771 + mc 2256 - mc 1833*mc 2256 - 2*mc 1771*mc 2256 + 2*mc 1771*mc 1833*mc 2256) + 2 * KeccakfPermAir.extraction.inter_6588 c row := by
    simp only [KeccakfPermAir.extraction.inter_6590, KeccakfPermAir.extraction.inter_6589, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6588 c row = (mc 1772 + mc 2257 - mc 1834*mc 2257 - 2*mc 1772*mc 2257 + 2*mc 1772*mc 1834*mc 2257) + 2 * KeccakfPermAir.extraction.inter_6586 c row := by
    simp only [KeccakfPermAir.extraction.inter_6588, KeccakfPermAir.extraction.inter_6587, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6586 c row = (mc 1773 + mc 2258 - mc 1835*mc 2258 - 2*mc 1773*mc 2258 + 2*mc 1773*mc 1835*mc 2258) + 2 * KeccakfPermAir.extraction.inter_6584 c row := by
    simp only [KeccakfPermAir.extraction.inter_6586, KeccakfPermAir.extraction.inter_6585, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6584 c row = (mc 1774 + mc 2259 - mc 1836*mc 2259 - 2*mc 1774*mc 2259 + 2*mc 1774*mc 1836*mc 2259) + 2 * KeccakfPermAir.extraction.inter_6582 c row := by
    simp only [KeccakfPermAir.extraction.inter_6584, KeccakfPermAir.extraction.inter_6583, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6582 c row = (mc 1775 + mc 2260 - mc 1837*mc 2260 - 2*mc 1775*mc 2260 + 2*mc 1775*mc 1837*mc 2260) + 2 * KeccakfPermAir.extraction.inter_6580 c row := by
    simp only [KeccakfPermAir.extraction.inter_6582, KeccakfPermAir.extraction.inter_6581, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6580 c row = (mc 1776 + mc 2261 - mc 1838*mc 2261 - 2*mc 1776*mc 2261 + 2*mc 1776*mc 1838*mc 2261) + 2 * KeccakfPermAir.extraction.inter_6578 c row := by
    simp only [KeccakfPermAir.extraction.inter_6580, KeccakfPermAir.extraction.inter_6579, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6578 c row = (mc 1777 + mc 2262 - mc 1839*mc 2262 - 2*mc 1777*mc 2262 + 2*mc 1777*mc 1839*mc 2262) + 2 * KeccakfPermAir.extraction.inter_6576 c row := by
    simp only [KeccakfPermAir.extraction.inter_6578, KeccakfPermAir.extraction.inter_6577, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6576 c row = (mc 1778 + mc 2263 - mc 1840*mc 2263 - 2*mc 1778*mc 2263 + 2*mc 1778*mc 1840*mc 2263) + 2 * KeccakfPermAir.extraction.inter_6574 c row := by
    simp only [KeccakfPermAir.extraction.inter_6576, KeccakfPermAir.extraction.inter_6575, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6574 c row = (mc 1779 + mc 2264 - mc 1841*mc 2264 - 2*mc 1779*mc 2264 + 2*mc 1779*mc 1841*mc 2264) + 2 * KeccakfPermAir.extraction.inter_6572 c row := by
    simp only [KeccakfPermAir.extraction.inter_6574, KeccakfPermAir.extraction.inter_6573, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6572 c row = (mc 1780 + mc 2265 - mc 1842*mc 2265 - 2*mc 1780*mc 2265 + 2*mc 1780*mc 1842*mc 2265) + 2 * KeccakfPermAir.extraction.inter_6570 c row := by
    simp only [KeccakfPermAir.extraction.inter_6572, KeccakfPermAir.extraction.inter_6571, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6570 c row = (mc 1781 + mc 2266 - mc 1843*mc 2266 - 2*mc 1781*mc 2266 + 2*mc 1781*mc 1843*mc 2266) + 2 * KeccakfPermAir.extraction.inter_6568 c row := by
    simp only [KeccakfPermAir.extraction.inter_6570, KeccakfPermAir.extraction.inter_6569, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6568 c row = (mc 1782 + mc 2267 - mc 1844*mc 2267 - 2*mc 1782*mc 2267 + 2*mc 1782*mc 1844*mc 2267) + 2 * KeccakfPermAir.extraction.inter_6566 c row := by
    simp only [KeccakfPermAir.extraction.inter_6568, KeccakfPermAir.extraction.inter_6567, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6566 c row = (mc 1783 + mc 2268 - mc 1845*mc 2268 - 2*mc 1783*mc 2268 + 2*mc 1783*mc 1845*mc 2268) + 2 * KeccakfPermAir.extraction.inter_6564 c row := by
    simp only [KeccakfPermAir.extraction.inter_6566, KeccakfPermAir.extraction.inter_6565, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6564 c row = (mc 1784 + mc 2269 - mc 1846*mc 2269 - 2*mc 1784*mc 2269 + 2*mc 1784*mc 1846*mc 2269) + 2 * KeccakfPermAir.extraction.inter_6562 c row := by
    simp only [KeccakfPermAir.extraction.inter_6564, KeccakfPermAir.extraction.inter_6563, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6562 c row = (mc 1785 + mc 2270 - mc 1847*mc 2270 - 2*mc 1785*mc 2270 + 2*mc 1785*mc 1847*mc 2270) := by
    simp only [KeccakfPermAir.extraction.inter_6562, KeccakfPermAir.extraction.inter_6561, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_3002 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3002 c row) :
    ((mc 1848 + mc 995 - mc 2271*mc 995 - 2*mc 1848*mc 995 + 2*mc 1848*mc 2271*mc 995) + 2*(mc 1849 + mc 996 - mc 2272*mc 996 - 2*mc 1849*mc 996 + 2*mc 1849*mc 2272*mc 996) + 4*(mc 1850 + mc 997 - mc 2209*mc 997 - 2*mc 1850*mc 997 + 2*mc 1850*mc 2209*mc 997) + 8*(mc 1851 + mc 998 - mc 2210*mc 998 - 2*mc 1851*mc 998 + 2*mc 1851*mc 2210*mc 998) + 16*(mc 1852 + mc 999 - mc 2211*mc 999 - 2*mc 1852*mc 999 + 2*mc 1852*mc 2211*mc 999) + 32*(mc 1853 + mc 1000 - mc 2212*mc 1000 - 2*mc 1853*mc 1000 + 2*mc 1853*mc 2212*mc 1000) + 64*(mc 1854 + mc 1001 - mc 2213*mc 1001 - 2*mc 1854*mc 1001 + 2*mc 1854*mc 2213*mc 1001) + 128*(mc 1855 + mc 1002 - mc 2214*mc 1002 - 2*mc 1855*mc 1002 + 2*mc 1855*mc 2214*mc 1002) + 256*(mc 1856 + mc 1003 - mc 2215*mc 1003 - 2*mc 1856*mc 1003 + 2*mc 1856*mc 2215*mc 1003) + 512*(mc 1857 + mc 1004 - mc 2216*mc 1004 - 2*mc 1857*mc 1004 + 2*mc 1857*mc 2216*mc 1004) + 1024*(mc 1858 + mc 1005 - mc 2217*mc 1005 - 2*mc 1858*mc 1005 + 2*mc 1858*mc 2217*mc 1005) + 2048*(mc 1859 + mc 1006 - mc 2218*mc 1006 - 2*mc 1859*mc 1006 + 2*mc 1859*mc 2218*mc 1006) + 4096*(mc 1860 + mc 1007 - mc 2219*mc 1007 - 2*mc 1860*mc 1007 + 2*mc 1860*mc 2219*mc 1007) + 8192*(mc 1861 + mc 1008 - mc 2220*mc 1008 - 2*mc 1861*mc 1008 + 2*mc 1861*mc 2220*mc 1008) + 16384*(mc 1862 + mc 1009 - mc 2221*mc 1009 - 2*mc 1862*mc 1009 + 2*mc 1862*mc 2221*mc 1009) + 32768*(mc 1863 + mc 1010 - mc 2222*mc 1010 - 2*mc 1863*mc 1010 + 2*mc 1863*mc 2222*mc 1010)) - mc 2557 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_3002, KeccakfPermAir.extraction.inter_6622, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6621 c row = (mc 1849 + mc 996 - mc 2272*mc 996 - 2*mc 1849*mc 996 + 2*mc 1849*mc 2272*mc 996) + 2 * KeccakfPermAir.extraction.inter_6619 c row := by
    simp only [KeccakfPermAir.extraction.inter_6621, KeccakfPermAir.extraction.inter_6620, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6619 c row = (mc 1850 + mc 997 - mc 2209*mc 997 - 2*mc 1850*mc 997 + 2*mc 1850*mc 2209*mc 997) + 2 * KeccakfPermAir.extraction.inter_6617 c row := by
    simp only [KeccakfPermAir.extraction.inter_6619, KeccakfPermAir.extraction.inter_6618, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6617 c row = (mc 1851 + mc 998 - mc 2210*mc 998 - 2*mc 1851*mc 998 + 2*mc 1851*mc 2210*mc 998) + 2 * KeccakfPermAir.extraction.inter_6615 c row := by
    simp only [KeccakfPermAir.extraction.inter_6617, KeccakfPermAir.extraction.inter_6616, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6615 c row = (mc 1852 + mc 999 - mc 2211*mc 999 - 2*mc 1852*mc 999 + 2*mc 1852*mc 2211*mc 999) + 2 * KeccakfPermAir.extraction.inter_6613 c row := by
    simp only [KeccakfPermAir.extraction.inter_6615, KeccakfPermAir.extraction.inter_6614, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6613 c row = (mc 1853 + mc 1000 - mc 2212*mc 1000 - 2*mc 1853*mc 1000 + 2*mc 1853*mc 2212*mc 1000) + 2 * KeccakfPermAir.extraction.inter_6611 c row := by
    simp only [KeccakfPermAir.extraction.inter_6613, KeccakfPermAir.extraction.inter_6612, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6611 c row = (mc 1854 + mc 1001 - mc 2213*mc 1001 - 2*mc 1854*mc 1001 + 2*mc 1854*mc 2213*mc 1001) + 2 * KeccakfPermAir.extraction.inter_6609 c row := by
    simp only [KeccakfPermAir.extraction.inter_6611, KeccakfPermAir.extraction.inter_6610, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6609 c row = (mc 1855 + mc 1002 - mc 2214*mc 1002 - 2*mc 1855*mc 1002 + 2*mc 1855*mc 2214*mc 1002) + 2 * KeccakfPermAir.extraction.inter_6607 c row := by
    simp only [KeccakfPermAir.extraction.inter_6609, KeccakfPermAir.extraction.inter_6608, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6607 c row = (mc 1856 + mc 1003 - mc 2215*mc 1003 - 2*mc 1856*mc 1003 + 2*mc 1856*mc 2215*mc 1003) + 2 * KeccakfPermAir.extraction.inter_6605 c row := by
    simp only [KeccakfPermAir.extraction.inter_6607, KeccakfPermAir.extraction.inter_6606, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6605 c row = (mc 1857 + mc 1004 - mc 2216*mc 1004 - 2*mc 1857*mc 1004 + 2*mc 1857*mc 2216*mc 1004) + 2 * KeccakfPermAir.extraction.inter_6603 c row := by
    simp only [KeccakfPermAir.extraction.inter_6605, KeccakfPermAir.extraction.inter_6604, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6603 c row = (mc 1858 + mc 1005 - mc 2217*mc 1005 - 2*mc 1858*mc 1005 + 2*mc 1858*mc 2217*mc 1005) + 2 * KeccakfPermAir.extraction.inter_6601 c row := by
    simp only [KeccakfPermAir.extraction.inter_6603, KeccakfPermAir.extraction.inter_6602, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6601 c row = (mc 1859 + mc 1006 - mc 2218*mc 1006 - 2*mc 1859*mc 1006 + 2*mc 1859*mc 2218*mc 1006) + 2 * KeccakfPermAir.extraction.inter_6599 c row := by
    simp only [KeccakfPermAir.extraction.inter_6601, KeccakfPermAir.extraction.inter_6600, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6599 c row = (mc 1860 + mc 1007 - mc 2219*mc 1007 - 2*mc 1860*mc 1007 + 2*mc 1860*mc 2219*mc 1007) + 2 * KeccakfPermAir.extraction.inter_6597 c row := by
    simp only [KeccakfPermAir.extraction.inter_6599, KeccakfPermAir.extraction.inter_6598, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6597 c row = (mc 1861 + mc 1008 - mc 2220*mc 1008 - 2*mc 1861*mc 1008 + 2*mc 1861*mc 2220*mc 1008) + 2 * KeccakfPermAir.extraction.inter_6595 c row := by
    simp only [KeccakfPermAir.extraction.inter_6597, KeccakfPermAir.extraction.inter_6596, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6595 c row = (mc 1862 + mc 1009 - mc 2221*mc 1009 - 2*mc 1862*mc 1009 + 2*mc 1862*mc 2221*mc 1009) + 2 * KeccakfPermAir.extraction.inter_6593 c row := by
    simp only [KeccakfPermAir.extraction.inter_6595, KeccakfPermAir.extraction.inter_6594, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6593 c row = (mc 1863 + mc 1010 - mc 2222*mc 1010 - 2*mc 1863*mc 1010 + 2*mc 1863*mc 2222*mc 1010) := by
    simp only [KeccakfPermAir.extraction.inter_6593, KeccakfPermAir.extraction.inter_6592, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_3003 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3003 c row) :
    ((mc 1864 + mc 1011 - mc 2223*mc 1011 - 2*mc 1864*mc 1011 + 2*mc 1864*mc 2223*mc 1011) + 2*(mc 1865 + mc 1012 - mc 2224*mc 1012 - 2*mc 1865*mc 1012 + 2*mc 1865*mc 2224*mc 1012) + 4*(mc 1866 + mc 1013 - mc 2225*mc 1013 - 2*mc 1866*mc 1013 + 2*mc 1866*mc 2225*mc 1013) + 8*(mc 1867 + mc 1014 - mc 2226*mc 1014 - 2*mc 1867*mc 1014 + 2*mc 1867*mc 2226*mc 1014) + 16*(mc 1868 + mc 1015 - mc 2227*mc 1015 - 2*mc 1868*mc 1015 + 2*mc 1868*mc 2227*mc 1015) + 32*(mc 1869 + mc 1016 - mc 2228*mc 1016 - 2*mc 1869*mc 1016 + 2*mc 1869*mc 2228*mc 1016) + 64*(mc 1870 + mc 1017 - mc 2229*mc 1017 - 2*mc 1870*mc 1017 + 2*mc 1870*mc 2229*mc 1017) + 128*(mc 1871 + mc 1018 - mc 2230*mc 1018 - 2*mc 1871*mc 1018 + 2*mc 1871*mc 2230*mc 1018) + 256*(mc 1872 + mc 1019 - mc 2231*mc 1019 - 2*mc 1872*mc 1019 + 2*mc 1872*mc 2231*mc 1019) + 512*(mc 1873 + mc 1020 - mc 2232*mc 1020 - 2*mc 1873*mc 1020 + 2*mc 1873*mc 2232*mc 1020) + 1024*(mc 1874 + mc 1021 - mc 2233*mc 1021 - 2*mc 1874*mc 1021 + 2*mc 1874*mc 2233*mc 1021) + 2048*(mc 1875 + mc 1022 - mc 2234*mc 1022 - 2*mc 1875*mc 1022 + 2*mc 1875*mc 2234*mc 1022) + 4096*(mc 1876 + mc 1023 - mc 2235*mc 1023 - 2*mc 1876*mc 1023 + 2*mc 1876*mc 2235*mc 1023) + 8192*(mc 1877 + mc 1024 - mc 2236*mc 1024 - 2*mc 1877*mc 1024 + 2*mc 1877*mc 2236*mc 1024) + 16384*(mc 1878 + mc 1025 - mc 2237*mc 1025 - 2*mc 1878*mc 1025 + 2*mc 1878*mc 2237*mc 1025) + 32768*(mc 1879 + mc 1026 - mc 2238*mc 1026 - 2*mc 1879*mc 1026 + 2*mc 1879*mc 2238*mc 1026)) - mc 2558 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_3003, KeccakfPermAir.extraction.inter_6653, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6652 c row = (mc 1865 + mc 1012 - mc 2224*mc 1012 - 2*mc 1865*mc 1012 + 2*mc 1865*mc 2224*mc 1012) + 2 * KeccakfPermAir.extraction.inter_6650 c row := by
    simp only [KeccakfPermAir.extraction.inter_6652, KeccakfPermAir.extraction.inter_6651, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6650 c row = (mc 1866 + mc 1013 - mc 2225*mc 1013 - 2*mc 1866*mc 1013 + 2*mc 1866*mc 2225*mc 1013) + 2 * KeccakfPermAir.extraction.inter_6648 c row := by
    simp only [KeccakfPermAir.extraction.inter_6650, KeccakfPermAir.extraction.inter_6649, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6648 c row = (mc 1867 + mc 1014 - mc 2226*mc 1014 - 2*mc 1867*mc 1014 + 2*mc 1867*mc 2226*mc 1014) + 2 * KeccakfPermAir.extraction.inter_6646 c row := by
    simp only [KeccakfPermAir.extraction.inter_6648, KeccakfPermAir.extraction.inter_6647, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6646 c row = (mc 1868 + mc 1015 - mc 2227*mc 1015 - 2*mc 1868*mc 1015 + 2*mc 1868*mc 2227*mc 1015) + 2 * KeccakfPermAir.extraction.inter_6644 c row := by
    simp only [KeccakfPermAir.extraction.inter_6646, KeccakfPermAir.extraction.inter_6645, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6644 c row = (mc 1869 + mc 1016 - mc 2228*mc 1016 - 2*mc 1869*mc 1016 + 2*mc 1869*mc 2228*mc 1016) + 2 * KeccakfPermAir.extraction.inter_6642 c row := by
    simp only [KeccakfPermAir.extraction.inter_6644, KeccakfPermAir.extraction.inter_6643, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6642 c row = (mc 1870 + mc 1017 - mc 2229*mc 1017 - 2*mc 1870*mc 1017 + 2*mc 1870*mc 2229*mc 1017) + 2 * KeccakfPermAir.extraction.inter_6640 c row := by
    simp only [KeccakfPermAir.extraction.inter_6642, KeccakfPermAir.extraction.inter_6641, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6640 c row = (mc 1871 + mc 1018 - mc 2230*mc 1018 - 2*mc 1871*mc 1018 + 2*mc 1871*mc 2230*mc 1018) + 2 * KeccakfPermAir.extraction.inter_6638 c row := by
    simp only [KeccakfPermAir.extraction.inter_6640, KeccakfPermAir.extraction.inter_6639, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6638 c row = (mc 1872 + mc 1019 - mc 2231*mc 1019 - 2*mc 1872*mc 1019 + 2*mc 1872*mc 2231*mc 1019) + 2 * KeccakfPermAir.extraction.inter_6636 c row := by
    simp only [KeccakfPermAir.extraction.inter_6638, KeccakfPermAir.extraction.inter_6637, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6636 c row = (mc 1873 + mc 1020 - mc 2232*mc 1020 - 2*mc 1873*mc 1020 + 2*mc 1873*mc 2232*mc 1020) + 2 * KeccakfPermAir.extraction.inter_6634 c row := by
    simp only [KeccakfPermAir.extraction.inter_6636, KeccakfPermAir.extraction.inter_6635, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6634 c row = (mc 1874 + mc 1021 - mc 2233*mc 1021 - 2*mc 1874*mc 1021 + 2*mc 1874*mc 2233*mc 1021) + 2 * KeccakfPermAir.extraction.inter_6632 c row := by
    simp only [KeccakfPermAir.extraction.inter_6634, KeccakfPermAir.extraction.inter_6633, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6632 c row = (mc 1875 + mc 1022 - mc 2234*mc 1022 - 2*mc 1875*mc 1022 + 2*mc 1875*mc 2234*mc 1022) + 2 * KeccakfPermAir.extraction.inter_6630 c row := by
    simp only [KeccakfPermAir.extraction.inter_6632, KeccakfPermAir.extraction.inter_6631, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6630 c row = (mc 1876 + mc 1023 - mc 2235*mc 1023 - 2*mc 1876*mc 1023 + 2*mc 1876*mc 2235*mc 1023) + 2 * KeccakfPermAir.extraction.inter_6628 c row := by
    simp only [KeccakfPermAir.extraction.inter_6630, KeccakfPermAir.extraction.inter_6629, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6628 c row = (mc 1877 + mc 1024 - mc 2236*mc 1024 - 2*mc 1877*mc 1024 + 2*mc 1877*mc 2236*mc 1024) + 2 * KeccakfPermAir.extraction.inter_6626 c row := by
    simp only [KeccakfPermAir.extraction.inter_6628, KeccakfPermAir.extraction.inter_6627, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6626 c row = (mc 1878 + mc 1025 - mc 2237*mc 1025 - 2*mc 1878*mc 1025 + 2*mc 1878*mc 2237*mc 1025) + 2 * KeccakfPermAir.extraction.inter_6624 c row := by
    simp only [KeccakfPermAir.extraction.inter_6626, KeccakfPermAir.extraction.inter_6625, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6624 c row = (mc 1879 + mc 1026 - mc 2238*mc 1026 - 2*mc 1879*mc 1026 + 2*mc 1879*mc 2238*mc 1026) := by
    simp only [KeccakfPermAir.extraction.inter_6624, KeccakfPermAir.extraction.inter_6623, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_3004 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3004 c row) :
    ((mc 1880 + mc 1027 - mc 2239*mc 1027 - 2*mc 1880*mc 1027 + 2*mc 1880*mc 2239*mc 1027) + 2*(mc 1881 + mc 1028 - mc 2240*mc 1028 - 2*mc 1881*mc 1028 + 2*mc 1881*mc 2240*mc 1028) + 4*(mc 1882 + mc 1029 - mc 2241*mc 1029 - 2*mc 1882*mc 1029 + 2*mc 1882*mc 2241*mc 1029) + 8*(mc 1883 + mc 1030 - mc 2242*mc 1030 - 2*mc 1883*mc 1030 + 2*mc 1883*mc 2242*mc 1030) + 16*(mc 1884 + mc 1031 - mc 2243*mc 1031 - 2*mc 1884*mc 1031 + 2*mc 1884*mc 2243*mc 1031) + 32*(mc 1885 + mc 1032 - mc 2244*mc 1032 - 2*mc 1885*mc 1032 + 2*mc 1885*mc 2244*mc 1032) + 64*(mc 1886 + mc 1033 - mc 2245*mc 1033 - 2*mc 1886*mc 1033 + 2*mc 1886*mc 2245*mc 1033) + 128*(mc 1887 + mc 1034 - mc 2246*mc 1034 - 2*mc 1887*mc 1034 + 2*mc 1887*mc 2246*mc 1034) + 256*(mc 1888 + mc 1035 - mc 2247*mc 1035 - 2*mc 1888*mc 1035 + 2*mc 1888*mc 2247*mc 1035) + 512*(mc 1825 + mc 1036 - mc 2248*mc 1036 - 2*mc 1825*mc 1036 + 2*mc 1825*mc 2248*mc 1036) + 1024*(mc 1826 + mc 1037 - mc 2249*mc 1037 - 2*mc 1826*mc 1037 + 2*mc 1826*mc 2249*mc 1037) + 2048*(mc 1827 + mc 1038 - mc 2250*mc 1038 - 2*mc 1827*mc 1038 + 2*mc 1827*mc 2250*mc 1038) + 4096*(mc 1828 + mc 1039 - mc 2251*mc 1039 - 2*mc 1828*mc 1039 + 2*mc 1828*mc 2251*mc 1039) + 8192*(mc 1829 + mc 1040 - mc 2252*mc 1040 - 2*mc 1829*mc 1040 + 2*mc 1829*mc 2252*mc 1040) + 16384*(mc 1830 + mc 1041 - mc 2253*mc 1041 - 2*mc 1830*mc 1041 + 2*mc 1830*mc 2253*mc 1041) + 32768*(mc 1831 + mc 1042 - mc 2254*mc 1042 - 2*mc 1831*mc 1042 + 2*mc 1831*mc 2254*mc 1042)) - mc 2559 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_3004, KeccakfPermAir.extraction.inter_6684, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6683 c row = (mc 1881 + mc 1028 - mc 2240*mc 1028 - 2*mc 1881*mc 1028 + 2*mc 1881*mc 2240*mc 1028) + 2 * KeccakfPermAir.extraction.inter_6681 c row := by
    simp only [KeccakfPermAir.extraction.inter_6683, KeccakfPermAir.extraction.inter_6682, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6681 c row = (mc 1882 + mc 1029 - mc 2241*mc 1029 - 2*mc 1882*mc 1029 + 2*mc 1882*mc 2241*mc 1029) + 2 * KeccakfPermAir.extraction.inter_6679 c row := by
    simp only [KeccakfPermAir.extraction.inter_6681, KeccakfPermAir.extraction.inter_6680, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6679 c row = (mc 1883 + mc 1030 - mc 2242*mc 1030 - 2*mc 1883*mc 1030 + 2*mc 1883*mc 2242*mc 1030) + 2 * KeccakfPermAir.extraction.inter_6677 c row := by
    simp only [KeccakfPermAir.extraction.inter_6679, KeccakfPermAir.extraction.inter_6678, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6677 c row = (mc 1884 + mc 1031 - mc 2243*mc 1031 - 2*mc 1884*mc 1031 + 2*mc 1884*mc 2243*mc 1031) + 2 * KeccakfPermAir.extraction.inter_6675 c row := by
    simp only [KeccakfPermAir.extraction.inter_6677, KeccakfPermAir.extraction.inter_6676, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6675 c row = (mc 1885 + mc 1032 - mc 2244*mc 1032 - 2*mc 1885*mc 1032 + 2*mc 1885*mc 2244*mc 1032) + 2 * KeccakfPermAir.extraction.inter_6673 c row := by
    simp only [KeccakfPermAir.extraction.inter_6675, KeccakfPermAir.extraction.inter_6674, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6673 c row = (mc 1886 + mc 1033 - mc 2245*mc 1033 - 2*mc 1886*mc 1033 + 2*mc 1886*mc 2245*mc 1033) + 2 * KeccakfPermAir.extraction.inter_6671 c row := by
    simp only [KeccakfPermAir.extraction.inter_6673, KeccakfPermAir.extraction.inter_6672, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6671 c row = (mc 1887 + mc 1034 - mc 2246*mc 1034 - 2*mc 1887*mc 1034 + 2*mc 1887*mc 2246*mc 1034) + 2 * KeccakfPermAir.extraction.inter_6669 c row := by
    simp only [KeccakfPermAir.extraction.inter_6671, KeccakfPermAir.extraction.inter_6670, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6669 c row = (mc 1888 + mc 1035 - mc 2247*mc 1035 - 2*mc 1888*mc 1035 + 2*mc 1888*mc 2247*mc 1035) + 2 * KeccakfPermAir.extraction.inter_6667 c row := by
    simp only [KeccakfPermAir.extraction.inter_6669, KeccakfPermAir.extraction.inter_6668, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6667 c row = (mc 1825 + mc 1036 - mc 2248*mc 1036 - 2*mc 1825*mc 1036 + 2*mc 1825*mc 2248*mc 1036) + 2 * KeccakfPermAir.extraction.inter_6665 c row := by
    simp only [KeccakfPermAir.extraction.inter_6667, KeccakfPermAir.extraction.inter_6666, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6665 c row = (mc 1826 + mc 1037 - mc 2249*mc 1037 - 2*mc 1826*mc 1037 + 2*mc 1826*mc 2249*mc 1037) + 2 * KeccakfPermAir.extraction.inter_6663 c row := by
    simp only [KeccakfPermAir.extraction.inter_6665, KeccakfPermAir.extraction.inter_6664, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6663 c row = (mc 1827 + mc 1038 - mc 2250*mc 1038 - 2*mc 1827*mc 1038 + 2*mc 1827*mc 2250*mc 1038) + 2 * KeccakfPermAir.extraction.inter_6661 c row := by
    simp only [KeccakfPermAir.extraction.inter_6663, KeccakfPermAir.extraction.inter_6662, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6661 c row = (mc 1828 + mc 1039 - mc 2251*mc 1039 - 2*mc 1828*mc 1039 + 2*mc 1828*mc 2251*mc 1039) + 2 * KeccakfPermAir.extraction.inter_6659 c row := by
    simp only [KeccakfPermAir.extraction.inter_6661, KeccakfPermAir.extraction.inter_6660, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6659 c row = (mc 1829 + mc 1040 - mc 2252*mc 1040 - 2*mc 1829*mc 1040 + 2*mc 1829*mc 2252*mc 1040) + 2 * KeccakfPermAir.extraction.inter_6657 c row := by
    simp only [KeccakfPermAir.extraction.inter_6659, KeccakfPermAir.extraction.inter_6658, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6657 c row = (mc 1830 + mc 1041 - mc 2253*mc 1041 - 2*mc 1830*mc 1041 + 2*mc 1830*mc 2253*mc 1041) + 2 * KeccakfPermAir.extraction.inter_6655 c row := by
    simp only [KeccakfPermAir.extraction.inter_6657, KeccakfPermAir.extraction.inter_6656, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6655 c row = (mc 1831 + mc 1042 - mc 2254*mc 1042 - 2*mc 1831*mc 1042 + 2*mc 1831*mc 2254*mc 1042) := by
    simp only [KeccakfPermAir.extraction.inter_6655, KeccakfPermAir.extraction.inter_6654, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_3005 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3005 c row) :
    ((mc 1832 + mc 1043 - mc 2255*mc 1043 - 2*mc 1832*mc 1043 + 2*mc 1832*mc 2255*mc 1043) + 2*(mc 1833 + mc 1044 - mc 2256*mc 1044 - 2*mc 1833*mc 1044 + 2*mc 1833*mc 2256*mc 1044) + 4*(mc 1834 + mc 1045 - mc 2257*mc 1045 - 2*mc 1834*mc 1045 + 2*mc 1834*mc 2257*mc 1045) + 8*(mc 1835 + mc 1046 - mc 2258*mc 1046 - 2*mc 1835*mc 1046 + 2*mc 1835*mc 2258*mc 1046) + 16*(mc 1836 + mc 1047 - mc 2259*mc 1047 - 2*mc 1836*mc 1047 + 2*mc 1836*mc 2259*mc 1047) + 32*(mc 1837 + mc 1048 - mc 2260*mc 1048 - 2*mc 1837*mc 1048 + 2*mc 1837*mc 2260*mc 1048) + 64*(mc 1838 + mc 1049 - mc 2261*mc 1049 - 2*mc 1838*mc 1049 + 2*mc 1838*mc 2261*mc 1049) + 128*(mc 1839 + mc 1050 - mc 2262*mc 1050 - 2*mc 1839*mc 1050 + 2*mc 1839*mc 2262*mc 1050) + 256*(mc 1840 + mc 1051 - mc 2263*mc 1051 - 2*mc 1840*mc 1051 + 2*mc 1840*mc 2263*mc 1051) + 512*(mc 1841 + mc 1052 - mc 2264*mc 1052 - 2*mc 1841*mc 1052 + 2*mc 1841*mc 2264*mc 1052) + 1024*(mc 1842 + mc 1053 - mc 2265*mc 1053 - 2*mc 1842*mc 1053 + 2*mc 1842*mc 2265*mc 1053) + 2048*(mc 1843 + mc 1054 - mc 2266*mc 1054 - 2*mc 1843*mc 1054 + 2*mc 1843*mc 2266*mc 1054) + 4096*(mc 1844 + mc 1055 - mc 2267*mc 1055 - 2*mc 1844*mc 1055 + 2*mc 1844*mc 2267*mc 1055) + 8192*(mc 1845 + mc 1056 - mc 2268*mc 1056 - 2*mc 1845*mc 1056 + 2*mc 1845*mc 2268*mc 1056) + 16384*(mc 1846 + mc 993 - mc 2269*mc 993 - 2*mc 1846*mc 993 + 2*mc 1846*mc 2269*mc 993) + 32768*(mc 1847 + mc 994 - mc 2270*mc 994 - 2*mc 1847*mc 994 + 2*mc 1847*mc 2270*mc 994)) - mc 2560 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_3005, KeccakfPermAir.extraction.inter_6715, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6714 c row = (mc 1833 + mc 1044 - mc 2256*mc 1044 - 2*mc 1833*mc 1044 + 2*mc 1833*mc 2256*mc 1044) + 2 * KeccakfPermAir.extraction.inter_6712 c row := by
    simp only [KeccakfPermAir.extraction.inter_6714, KeccakfPermAir.extraction.inter_6713, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6712 c row = (mc 1834 + mc 1045 - mc 2257*mc 1045 - 2*mc 1834*mc 1045 + 2*mc 1834*mc 2257*mc 1045) + 2 * KeccakfPermAir.extraction.inter_6710 c row := by
    simp only [KeccakfPermAir.extraction.inter_6712, KeccakfPermAir.extraction.inter_6711, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6710 c row = (mc 1835 + mc 1046 - mc 2258*mc 1046 - 2*mc 1835*mc 1046 + 2*mc 1835*mc 2258*mc 1046) + 2 * KeccakfPermAir.extraction.inter_6708 c row := by
    simp only [KeccakfPermAir.extraction.inter_6710, KeccakfPermAir.extraction.inter_6709, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6708 c row = (mc 1836 + mc 1047 - mc 2259*mc 1047 - 2*mc 1836*mc 1047 + 2*mc 1836*mc 2259*mc 1047) + 2 * KeccakfPermAir.extraction.inter_6706 c row := by
    simp only [KeccakfPermAir.extraction.inter_6708, KeccakfPermAir.extraction.inter_6707, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6706 c row = (mc 1837 + mc 1048 - mc 2260*mc 1048 - 2*mc 1837*mc 1048 + 2*mc 1837*mc 2260*mc 1048) + 2 * KeccakfPermAir.extraction.inter_6704 c row := by
    simp only [KeccakfPermAir.extraction.inter_6706, KeccakfPermAir.extraction.inter_6705, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6704 c row = (mc 1838 + mc 1049 - mc 2261*mc 1049 - 2*mc 1838*mc 1049 + 2*mc 1838*mc 2261*mc 1049) + 2 * KeccakfPermAir.extraction.inter_6702 c row := by
    simp only [KeccakfPermAir.extraction.inter_6704, KeccakfPermAir.extraction.inter_6703, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6702 c row = (mc 1839 + mc 1050 - mc 2262*mc 1050 - 2*mc 1839*mc 1050 + 2*mc 1839*mc 2262*mc 1050) + 2 * KeccakfPermAir.extraction.inter_6700 c row := by
    simp only [KeccakfPermAir.extraction.inter_6702, KeccakfPermAir.extraction.inter_6701, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6700 c row = (mc 1840 + mc 1051 - mc 2263*mc 1051 - 2*mc 1840*mc 1051 + 2*mc 1840*mc 2263*mc 1051) + 2 * KeccakfPermAir.extraction.inter_6698 c row := by
    simp only [KeccakfPermAir.extraction.inter_6700, KeccakfPermAir.extraction.inter_6699, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6698 c row = (mc 1841 + mc 1052 - mc 2264*mc 1052 - 2*mc 1841*mc 1052 + 2*mc 1841*mc 2264*mc 1052) + 2 * KeccakfPermAir.extraction.inter_6696 c row := by
    simp only [KeccakfPermAir.extraction.inter_6698, KeccakfPermAir.extraction.inter_6697, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6696 c row = (mc 1842 + mc 1053 - mc 2265*mc 1053 - 2*mc 1842*mc 1053 + 2*mc 1842*mc 2265*mc 1053) + 2 * KeccakfPermAir.extraction.inter_6694 c row := by
    simp only [KeccakfPermAir.extraction.inter_6696, KeccakfPermAir.extraction.inter_6695, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6694 c row = (mc 1843 + mc 1054 - mc 2266*mc 1054 - 2*mc 1843*mc 1054 + 2*mc 1843*mc 2266*mc 1054) + 2 * KeccakfPermAir.extraction.inter_6692 c row := by
    simp only [KeccakfPermAir.extraction.inter_6694, KeccakfPermAir.extraction.inter_6693, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6692 c row = (mc 1844 + mc 1055 - mc 2267*mc 1055 - 2*mc 1844*mc 1055 + 2*mc 1844*mc 2267*mc 1055) + 2 * KeccakfPermAir.extraction.inter_6690 c row := by
    simp only [KeccakfPermAir.extraction.inter_6692, KeccakfPermAir.extraction.inter_6691, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6690 c row = (mc 1845 + mc 1056 - mc 2268*mc 1056 - 2*mc 1845*mc 1056 + 2*mc 1845*mc 2268*mc 1056) + 2 * KeccakfPermAir.extraction.inter_6688 c row := by
    simp only [KeccakfPermAir.extraction.inter_6690, KeccakfPermAir.extraction.inter_6689, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6688 c row = (mc 1846 + mc 993 - mc 2269*mc 993 - 2*mc 1846*mc 993 + 2*mc 1846*mc 2269*mc 993) + 2 * KeccakfPermAir.extraction.inter_6686 c row := by
    simp only [KeccakfPermAir.extraction.inter_6688, KeccakfPermAir.extraction.inter_6687, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6686 c row = (mc 1847 + mc 994 - mc 2270*mc 994 - 2*mc 1847*mc 994 + 2*mc 1847*mc 2270*mc 994) := by
    simp only [KeccakfPermAir.extraction.inter_6686, KeccakfPermAir.extraction.inter_6685, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_3006 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3006 c row) :
    ((mc 2271 + mc 1386 - mc 995*mc 1386 - 2*mc 2271*mc 1386 + 2*mc 2271*mc 995*mc 1386) + 2*(mc 2272 + mc 1387 - mc 996*mc 1387 - 2*mc 2272*mc 1387 + 2*mc 2272*mc 996*mc 1387) + 4*(mc 2209 + mc 1388 - mc 997*mc 1388 - 2*mc 2209*mc 1388 + 2*mc 2209*mc 997*mc 1388) + 8*(mc 2210 + mc 1389 - mc 998*mc 1389 - 2*mc 2210*mc 1389 + 2*mc 2210*mc 998*mc 1389) + 16*(mc 2211 + mc 1390 - mc 999*mc 1390 - 2*mc 2211*mc 1390 + 2*mc 2211*mc 999*mc 1390) + 32*(mc 2212 + mc 1391 - mc 1000*mc 1391 - 2*mc 2212*mc 1391 + 2*mc 2212*mc 1000*mc 1391) + 64*(mc 2213 + mc 1392 - mc 1001*mc 1392 - 2*mc 2213*mc 1392 + 2*mc 2213*mc 1001*mc 1392) + 128*(mc 2214 + mc 1393 - mc 1002*mc 1393 - 2*mc 2214*mc 1393 + 2*mc 2214*mc 1002*mc 1393) + 256*(mc 2215 + mc 1394 - mc 1003*mc 1394 - 2*mc 2215*mc 1394 + 2*mc 2215*mc 1003*mc 1394) + 512*(mc 2216 + mc 1395 - mc 1004*mc 1395 - 2*mc 2216*mc 1395 + 2*mc 2216*mc 1004*mc 1395) + 1024*(mc 2217 + mc 1396 - mc 1005*mc 1396 - 2*mc 2217*mc 1396 + 2*mc 2217*mc 1005*mc 1396) + 2048*(mc 2218 + mc 1397 - mc 1006*mc 1397 - 2*mc 2218*mc 1397 + 2*mc 2218*mc 1006*mc 1397) + 4096*(mc 2219 + mc 1398 - mc 1007*mc 1398 - 2*mc 2219*mc 1398 + 2*mc 2219*mc 1007*mc 1398) + 8192*(mc 2220 + mc 1399 - mc 1008*mc 1399 - 2*mc 2220*mc 1399 + 2*mc 2220*mc 1008*mc 1399) + 16384*(mc 2221 + mc 1400 - mc 1009*mc 1400 - 2*mc 2221*mc 1400 + 2*mc 2221*mc 1009*mc 1400) + 32768*(mc 2222 + mc 1401 - mc 1010*mc 1401 - 2*mc 2222*mc 1401 + 2*mc 2222*mc 1010*mc 1401)) - mc 2561 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_3006, KeccakfPermAir.extraction.inter_6746, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6745 c row = (mc 2272 + mc 1387 - mc 996*mc 1387 - 2*mc 2272*mc 1387 + 2*mc 2272*mc 996*mc 1387) + 2 * KeccakfPermAir.extraction.inter_6743 c row := by
    simp only [KeccakfPermAir.extraction.inter_6745, KeccakfPermAir.extraction.inter_6744, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6743 c row = (mc 2209 + mc 1388 - mc 997*mc 1388 - 2*mc 2209*mc 1388 + 2*mc 2209*mc 997*mc 1388) + 2 * KeccakfPermAir.extraction.inter_6741 c row := by
    simp only [KeccakfPermAir.extraction.inter_6743, KeccakfPermAir.extraction.inter_6742, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6741 c row = (mc 2210 + mc 1389 - mc 998*mc 1389 - 2*mc 2210*mc 1389 + 2*mc 2210*mc 998*mc 1389) + 2 * KeccakfPermAir.extraction.inter_6739 c row := by
    simp only [KeccakfPermAir.extraction.inter_6741, KeccakfPermAir.extraction.inter_6740, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6739 c row = (mc 2211 + mc 1390 - mc 999*mc 1390 - 2*mc 2211*mc 1390 + 2*mc 2211*mc 999*mc 1390) + 2 * KeccakfPermAir.extraction.inter_6737 c row := by
    simp only [KeccakfPermAir.extraction.inter_6739, KeccakfPermAir.extraction.inter_6738, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6737 c row = (mc 2212 + mc 1391 - mc 1000*mc 1391 - 2*mc 2212*mc 1391 + 2*mc 2212*mc 1000*mc 1391) + 2 * KeccakfPermAir.extraction.inter_6735 c row := by
    simp only [KeccakfPermAir.extraction.inter_6737, KeccakfPermAir.extraction.inter_6736, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6735 c row = (mc 2213 + mc 1392 - mc 1001*mc 1392 - 2*mc 2213*mc 1392 + 2*mc 2213*mc 1001*mc 1392) + 2 * KeccakfPermAir.extraction.inter_6733 c row := by
    simp only [KeccakfPermAir.extraction.inter_6735, KeccakfPermAir.extraction.inter_6734, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6733 c row = (mc 2214 + mc 1393 - mc 1002*mc 1393 - 2*mc 2214*mc 1393 + 2*mc 2214*mc 1002*mc 1393) + 2 * KeccakfPermAir.extraction.inter_6731 c row := by
    simp only [KeccakfPermAir.extraction.inter_6733, KeccakfPermAir.extraction.inter_6732, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6731 c row = (mc 2215 + mc 1394 - mc 1003*mc 1394 - 2*mc 2215*mc 1394 + 2*mc 2215*mc 1003*mc 1394) + 2 * KeccakfPermAir.extraction.inter_6729 c row := by
    simp only [KeccakfPermAir.extraction.inter_6731, KeccakfPermAir.extraction.inter_6730, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6729 c row = (mc 2216 + mc 1395 - mc 1004*mc 1395 - 2*mc 2216*mc 1395 + 2*mc 2216*mc 1004*mc 1395) + 2 * KeccakfPermAir.extraction.inter_6727 c row := by
    simp only [KeccakfPermAir.extraction.inter_6729, KeccakfPermAir.extraction.inter_6728, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6727 c row = (mc 2217 + mc 1396 - mc 1005*mc 1396 - 2*mc 2217*mc 1396 + 2*mc 2217*mc 1005*mc 1396) + 2 * KeccakfPermAir.extraction.inter_6725 c row := by
    simp only [KeccakfPermAir.extraction.inter_6727, KeccakfPermAir.extraction.inter_6726, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6725 c row = (mc 2218 + mc 1397 - mc 1006*mc 1397 - 2*mc 2218*mc 1397 + 2*mc 2218*mc 1006*mc 1397) + 2 * KeccakfPermAir.extraction.inter_6723 c row := by
    simp only [KeccakfPermAir.extraction.inter_6725, KeccakfPermAir.extraction.inter_6724, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6723 c row = (mc 2219 + mc 1398 - mc 1007*mc 1398 - 2*mc 2219*mc 1398 + 2*mc 2219*mc 1007*mc 1398) + 2 * KeccakfPermAir.extraction.inter_6721 c row := by
    simp only [KeccakfPermAir.extraction.inter_6723, KeccakfPermAir.extraction.inter_6722, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6721 c row = (mc 2220 + mc 1399 - mc 1008*mc 1399 - 2*mc 2220*mc 1399 + 2*mc 2220*mc 1008*mc 1399) + 2 * KeccakfPermAir.extraction.inter_6719 c row := by
    simp only [KeccakfPermAir.extraction.inter_6721, KeccakfPermAir.extraction.inter_6720, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6719 c row = (mc 2221 + mc 1400 - mc 1009*mc 1400 - 2*mc 2221*mc 1400 + 2*mc 2221*mc 1009*mc 1400) + 2 * KeccakfPermAir.extraction.inter_6717 c row := by
    simp only [KeccakfPermAir.extraction.inter_6719, KeccakfPermAir.extraction.inter_6718, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6717 c row = (mc 2222 + mc 1401 - mc 1010*mc 1401 - 2*mc 2222*mc 1401 + 2*mc 2222*mc 1010*mc 1401) := by
    simp only [KeccakfPermAir.extraction.inter_6717, KeccakfPermAir.extraction.inter_6716, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_3007 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3007 c row) :
    ((mc 2223 + mc 1402 - mc 1011*mc 1402 - 2*mc 2223*mc 1402 + 2*mc 2223*mc 1011*mc 1402) + 2*(mc 2224 + mc 1403 - mc 1012*mc 1403 - 2*mc 2224*mc 1403 + 2*mc 2224*mc 1012*mc 1403) + 4*(mc 2225 + mc 1404 - mc 1013*mc 1404 - 2*mc 2225*mc 1404 + 2*mc 2225*mc 1013*mc 1404) + 8*(mc 2226 + mc 1405 - mc 1014*mc 1405 - 2*mc 2226*mc 1405 + 2*mc 2226*mc 1014*mc 1405) + 16*(mc 2227 + mc 1406 - mc 1015*mc 1406 - 2*mc 2227*mc 1406 + 2*mc 2227*mc 1015*mc 1406) + 32*(mc 2228 + mc 1407 - mc 1016*mc 1407 - 2*mc 2228*mc 1407 + 2*mc 2228*mc 1016*mc 1407) + 64*(mc 2229 + mc 1408 - mc 1017*mc 1408 - 2*mc 2229*mc 1408 + 2*mc 2229*mc 1017*mc 1408) + 128*(mc 2230 + mc 1409 - mc 1018*mc 1409 - 2*mc 2230*mc 1409 + 2*mc 2230*mc 1018*mc 1409) + 256*(mc 2231 + mc 1410 - mc 1019*mc 1410 - 2*mc 2231*mc 1410 + 2*mc 2231*mc 1019*mc 1410) + 512*(mc 2232 + mc 1411 - mc 1020*mc 1411 - 2*mc 2232*mc 1411 + 2*mc 2232*mc 1020*mc 1411) + 1024*(mc 2233 + mc 1412 - mc 1021*mc 1412 - 2*mc 2233*mc 1412 + 2*mc 2233*mc 1021*mc 1412) + 2048*(mc 2234 + mc 1413 - mc 1022*mc 1413 - 2*mc 2234*mc 1413 + 2*mc 2234*mc 1022*mc 1413) + 4096*(mc 2235 + mc 1414 - mc 1023*mc 1414 - 2*mc 2235*mc 1414 + 2*mc 2235*mc 1023*mc 1414) + 8192*(mc 2236 + mc 1415 - mc 1024*mc 1415 - 2*mc 2236*mc 1415 + 2*mc 2236*mc 1024*mc 1415) + 16384*(mc 2237 + mc 1416 - mc 1025*mc 1416 - 2*mc 2237*mc 1416 + 2*mc 2237*mc 1025*mc 1416) + 32768*(mc 2238 + mc 1417 - mc 1026*mc 1417 - 2*mc 2238*mc 1417 + 2*mc 2238*mc 1026*mc 1417)) - mc 2562 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_3007, KeccakfPermAir.extraction.inter_6777, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6776 c row = (mc 2224 + mc 1403 - mc 1012*mc 1403 - 2*mc 2224*mc 1403 + 2*mc 2224*mc 1012*mc 1403) + 2 * KeccakfPermAir.extraction.inter_6774 c row := by
    simp only [KeccakfPermAir.extraction.inter_6776, KeccakfPermAir.extraction.inter_6775, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6774 c row = (mc 2225 + mc 1404 - mc 1013*mc 1404 - 2*mc 2225*mc 1404 + 2*mc 2225*mc 1013*mc 1404) + 2 * KeccakfPermAir.extraction.inter_6772 c row := by
    simp only [KeccakfPermAir.extraction.inter_6774, KeccakfPermAir.extraction.inter_6773, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6772 c row = (mc 2226 + mc 1405 - mc 1014*mc 1405 - 2*mc 2226*mc 1405 + 2*mc 2226*mc 1014*mc 1405) + 2 * KeccakfPermAir.extraction.inter_6770 c row := by
    simp only [KeccakfPermAir.extraction.inter_6772, KeccakfPermAir.extraction.inter_6771, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6770 c row = (mc 2227 + mc 1406 - mc 1015*mc 1406 - 2*mc 2227*mc 1406 + 2*mc 2227*mc 1015*mc 1406) + 2 * KeccakfPermAir.extraction.inter_6768 c row := by
    simp only [KeccakfPermAir.extraction.inter_6770, KeccakfPermAir.extraction.inter_6769, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6768 c row = (mc 2228 + mc 1407 - mc 1016*mc 1407 - 2*mc 2228*mc 1407 + 2*mc 2228*mc 1016*mc 1407) + 2 * KeccakfPermAir.extraction.inter_6766 c row := by
    simp only [KeccakfPermAir.extraction.inter_6768, KeccakfPermAir.extraction.inter_6767, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6766 c row = (mc 2229 + mc 1408 - mc 1017*mc 1408 - 2*mc 2229*mc 1408 + 2*mc 2229*mc 1017*mc 1408) + 2 * KeccakfPermAir.extraction.inter_6764 c row := by
    simp only [KeccakfPermAir.extraction.inter_6766, KeccakfPermAir.extraction.inter_6765, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6764 c row = (mc 2230 + mc 1409 - mc 1018*mc 1409 - 2*mc 2230*mc 1409 + 2*mc 2230*mc 1018*mc 1409) + 2 * KeccakfPermAir.extraction.inter_6762 c row := by
    simp only [KeccakfPermAir.extraction.inter_6764, KeccakfPermAir.extraction.inter_6763, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6762 c row = (mc 2231 + mc 1410 - mc 1019*mc 1410 - 2*mc 2231*mc 1410 + 2*mc 2231*mc 1019*mc 1410) + 2 * KeccakfPermAir.extraction.inter_6760 c row := by
    simp only [KeccakfPermAir.extraction.inter_6762, KeccakfPermAir.extraction.inter_6761, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6760 c row = (mc 2232 + mc 1411 - mc 1020*mc 1411 - 2*mc 2232*mc 1411 + 2*mc 2232*mc 1020*mc 1411) + 2 * KeccakfPermAir.extraction.inter_6758 c row := by
    simp only [KeccakfPermAir.extraction.inter_6760, KeccakfPermAir.extraction.inter_6759, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6758 c row = (mc 2233 + mc 1412 - mc 1021*mc 1412 - 2*mc 2233*mc 1412 + 2*mc 2233*mc 1021*mc 1412) + 2 * KeccakfPermAir.extraction.inter_6756 c row := by
    simp only [KeccakfPermAir.extraction.inter_6758, KeccakfPermAir.extraction.inter_6757, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6756 c row = (mc 2234 + mc 1413 - mc 1022*mc 1413 - 2*mc 2234*mc 1413 + 2*mc 2234*mc 1022*mc 1413) + 2 * KeccakfPermAir.extraction.inter_6754 c row := by
    simp only [KeccakfPermAir.extraction.inter_6756, KeccakfPermAir.extraction.inter_6755, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6754 c row = (mc 2235 + mc 1414 - mc 1023*mc 1414 - 2*mc 2235*mc 1414 + 2*mc 2235*mc 1023*mc 1414) + 2 * KeccakfPermAir.extraction.inter_6752 c row := by
    simp only [KeccakfPermAir.extraction.inter_6754, KeccakfPermAir.extraction.inter_6753, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6752 c row = (mc 2236 + mc 1415 - mc 1024*mc 1415 - 2*mc 2236*mc 1415 + 2*mc 2236*mc 1024*mc 1415) + 2 * KeccakfPermAir.extraction.inter_6750 c row := by
    simp only [KeccakfPermAir.extraction.inter_6752, KeccakfPermAir.extraction.inter_6751, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6750 c row = (mc 2237 + mc 1416 - mc 1025*mc 1416 - 2*mc 2237*mc 1416 + 2*mc 2237*mc 1025*mc 1416) + 2 * KeccakfPermAir.extraction.inter_6748 c row := by
    simp only [KeccakfPermAir.extraction.inter_6750, KeccakfPermAir.extraction.inter_6749, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6748 c row = (mc 2238 + mc 1417 - mc 1026*mc 1417 - 2*mc 2238*mc 1417 + 2*mc 2238*mc 1026*mc 1417) := by
    simp only [KeccakfPermAir.extraction.inter_6748, KeccakfPermAir.extraction.inter_6747, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_3008 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3008 c row) :
    ((mc 2239 + mc 1418 - mc 1027*mc 1418 - 2*mc 2239*mc 1418 + 2*mc 2239*mc 1027*mc 1418) + 2*(mc 2240 + mc 1419 - mc 1028*mc 1419 - 2*mc 2240*mc 1419 + 2*mc 2240*mc 1028*mc 1419) + 4*(mc 2241 + mc 1420 - mc 1029*mc 1420 - 2*mc 2241*mc 1420 + 2*mc 2241*mc 1029*mc 1420) + 8*(mc 2242 + mc 1421 - mc 1030*mc 1421 - 2*mc 2242*mc 1421 + 2*mc 2242*mc 1030*mc 1421) + 16*(mc 2243 + mc 1422 - mc 1031*mc 1422 - 2*mc 2243*mc 1422 + 2*mc 2243*mc 1031*mc 1422) + 32*(mc 2244 + mc 1423 - mc 1032*mc 1423 - 2*mc 2244*mc 1423 + 2*mc 2244*mc 1032*mc 1423) + 64*(mc 2245 + mc 1424 - mc 1033*mc 1424 - 2*mc 2245*mc 1424 + 2*mc 2245*mc 1033*mc 1424) + 128*(mc 2246 + mc 1425 - mc 1034*mc 1425 - 2*mc 2246*mc 1425 + 2*mc 2246*mc 1034*mc 1425) + 256*(mc 2247 + mc 1426 - mc 1035*mc 1426 - 2*mc 2247*mc 1426 + 2*mc 2247*mc 1035*mc 1426) + 512*(mc 2248 + mc 1427 - mc 1036*mc 1427 - 2*mc 2248*mc 1427 + 2*mc 2248*mc 1036*mc 1427) + 1024*(mc 2249 + mc 1428 - mc 1037*mc 1428 - 2*mc 2249*mc 1428 + 2*mc 2249*mc 1037*mc 1428) + 2048*(mc 2250 + mc 1429 - mc 1038*mc 1429 - 2*mc 2250*mc 1429 + 2*mc 2250*mc 1038*mc 1429) + 4096*(mc 2251 + mc 1430 - mc 1039*mc 1430 - 2*mc 2251*mc 1430 + 2*mc 2251*mc 1039*mc 1430) + 8192*(mc 2252 + mc 1431 - mc 1040*mc 1431 - 2*mc 2252*mc 1431 + 2*mc 2252*mc 1040*mc 1431) + 16384*(mc 2253 + mc 1432 - mc 1041*mc 1432 - 2*mc 2253*mc 1432 + 2*mc 2253*mc 1041*mc 1432) + 32768*(mc 2254 + mc 1433 - mc 1042*mc 1433 - 2*mc 2254*mc 1433 + 2*mc 2254*mc 1042*mc 1433)) - mc 2563 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_3008, KeccakfPermAir.extraction.inter_6808, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6807 c row = (mc 2240 + mc 1419 - mc 1028*mc 1419 - 2*mc 2240*mc 1419 + 2*mc 2240*mc 1028*mc 1419) + 2 * KeccakfPermAir.extraction.inter_6805 c row := by
    simp only [KeccakfPermAir.extraction.inter_6807, KeccakfPermAir.extraction.inter_6806, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6805 c row = (mc 2241 + mc 1420 - mc 1029*mc 1420 - 2*mc 2241*mc 1420 + 2*mc 2241*mc 1029*mc 1420) + 2 * KeccakfPermAir.extraction.inter_6803 c row := by
    simp only [KeccakfPermAir.extraction.inter_6805, KeccakfPermAir.extraction.inter_6804, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6803 c row = (mc 2242 + mc 1421 - mc 1030*mc 1421 - 2*mc 2242*mc 1421 + 2*mc 2242*mc 1030*mc 1421) + 2 * KeccakfPermAir.extraction.inter_6801 c row := by
    simp only [KeccakfPermAir.extraction.inter_6803, KeccakfPermAir.extraction.inter_6802, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6801 c row = (mc 2243 + mc 1422 - mc 1031*mc 1422 - 2*mc 2243*mc 1422 + 2*mc 2243*mc 1031*mc 1422) + 2 * KeccakfPermAir.extraction.inter_6799 c row := by
    simp only [KeccakfPermAir.extraction.inter_6801, KeccakfPermAir.extraction.inter_6800, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6799 c row = (mc 2244 + mc 1423 - mc 1032*mc 1423 - 2*mc 2244*mc 1423 + 2*mc 2244*mc 1032*mc 1423) + 2 * KeccakfPermAir.extraction.inter_6797 c row := by
    simp only [KeccakfPermAir.extraction.inter_6799, KeccakfPermAir.extraction.inter_6798, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6797 c row = (mc 2245 + mc 1424 - mc 1033*mc 1424 - 2*mc 2245*mc 1424 + 2*mc 2245*mc 1033*mc 1424) + 2 * KeccakfPermAir.extraction.inter_6795 c row := by
    simp only [KeccakfPermAir.extraction.inter_6797, KeccakfPermAir.extraction.inter_6796, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6795 c row = (mc 2246 + mc 1425 - mc 1034*mc 1425 - 2*mc 2246*mc 1425 + 2*mc 2246*mc 1034*mc 1425) + 2 * KeccakfPermAir.extraction.inter_6793 c row := by
    simp only [KeccakfPermAir.extraction.inter_6795, KeccakfPermAir.extraction.inter_6794, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6793 c row = (mc 2247 + mc 1426 - mc 1035*mc 1426 - 2*mc 2247*mc 1426 + 2*mc 2247*mc 1035*mc 1426) + 2 * KeccakfPermAir.extraction.inter_6791 c row := by
    simp only [KeccakfPermAir.extraction.inter_6793, KeccakfPermAir.extraction.inter_6792, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6791 c row = (mc 2248 + mc 1427 - mc 1036*mc 1427 - 2*mc 2248*mc 1427 + 2*mc 2248*mc 1036*mc 1427) + 2 * KeccakfPermAir.extraction.inter_6789 c row := by
    simp only [KeccakfPermAir.extraction.inter_6791, KeccakfPermAir.extraction.inter_6790, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6789 c row = (mc 2249 + mc 1428 - mc 1037*mc 1428 - 2*mc 2249*mc 1428 + 2*mc 2249*mc 1037*mc 1428) + 2 * KeccakfPermAir.extraction.inter_6787 c row := by
    simp only [KeccakfPermAir.extraction.inter_6789, KeccakfPermAir.extraction.inter_6788, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6787 c row = (mc 2250 + mc 1429 - mc 1038*mc 1429 - 2*mc 2250*mc 1429 + 2*mc 2250*mc 1038*mc 1429) + 2 * KeccakfPermAir.extraction.inter_6785 c row := by
    simp only [KeccakfPermAir.extraction.inter_6787, KeccakfPermAir.extraction.inter_6786, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6785 c row = (mc 2251 + mc 1430 - mc 1039*mc 1430 - 2*mc 2251*mc 1430 + 2*mc 2251*mc 1039*mc 1430) + 2 * KeccakfPermAir.extraction.inter_6783 c row := by
    simp only [KeccakfPermAir.extraction.inter_6785, KeccakfPermAir.extraction.inter_6784, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6783 c row = (mc 2252 + mc 1431 - mc 1040*mc 1431 - 2*mc 2252*mc 1431 + 2*mc 2252*mc 1040*mc 1431) + 2 * KeccakfPermAir.extraction.inter_6781 c row := by
    simp only [KeccakfPermAir.extraction.inter_6783, KeccakfPermAir.extraction.inter_6782, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6781 c row = (mc 2253 + mc 1432 - mc 1041*mc 1432 - 2*mc 2253*mc 1432 + 2*mc 2253*mc 1041*mc 1432) + 2 * KeccakfPermAir.extraction.inter_6779 c row := by
    simp only [KeccakfPermAir.extraction.inter_6781, KeccakfPermAir.extraction.inter_6780, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6779 c row = (mc 2254 + mc 1433 - mc 1042*mc 1433 - 2*mc 2254*mc 1433 + 2*mc 2254*mc 1042*mc 1433) := by
    simp only [KeccakfPermAir.extraction.inter_6779, KeccakfPermAir.extraction.inter_6778, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

private theorem peel_chi_3009 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) {row : ℕ} (mc : ℕ → F)
    (hmc : ∀ col, Circuit.main c (id := 0) (column := col) (row := row) (rotation := 0) = mc col)
    (hx : KeccakfPermAir.extraction.constraint_3009 c row) :
    ((mc 2255 + mc 1434 - mc 1043*mc 1434 - 2*mc 2255*mc 1434 + 2*mc 2255*mc 1043*mc 1434) + 2*(mc 2256 + mc 1435 - mc 1044*mc 1435 - 2*mc 2256*mc 1435 + 2*mc 2256*mc 1044*mc 1435) + 4*(mc 2257 + mc 1436 - mc 1045*mc 1436 - 2*mc 2257*mc 1436 + 2*mc 2257*mc 1045*mc 1436) + 8*(mc 2258 + mc 1437 - mc 1046*mc 1437 - 2*mc 2258*mc 1437 + 2*mc 2258*mc 1046*mc 1437) + 16*(mc 2259 + mc 1438 - mc 1047*mc 1438 - 2*mc 2259*mc 1438 + 2*mc 2259*mc 1047*mc 1438) + 32*(mc 2260 + mc 1439 - mc 1048*mc 1439 - 2*mc 2260*mc 1439 + 2*mc 2260*mc 1048*mc 1439) + 64*(mc 2261 + mc 1440 - mc 1049*mc 1440 - 2*mc 2261*mc 1440 + 2*mc 2261*mc 1049*mc 1440) + 128*(mc 2262 + mc 1377 - mc 1050*mc 1377 - 2*mc 2262*mc 1377 + 2*mc 2262*mc 1050*mc 1377) + 256*(mc 2263 + mc 1378 - mc 1051*mc 1378 - 2*mc 2263*mc 1378 + 2*mc 2263*mc 1051*mc 1378) + 512*(mc 2264 + mc 1379 - mc 1052*mc 1379 - 2*mc 2264*mc 1379 + 2*mc 2264*mc 1052*mc 1379) + 1024*(mc 2265 + mc 1380 - mc 1053*mc 1380 - 2*mc 2265*mc 1380 + 2*mc 2265*mc 1053*mc 1380) + 2048*(mc 2266 + mc 1381 - mc 1054*mc 1381 - 2*mc 2266*mc 1381 + 2*mc 2266*mc 1054*mc 1381) + 4096*(mc 2267 + mc 1382 - mc 1055*mc 1382 - 2*mc 2267*mc 1382 + 2*mc 2267*mc 1055*mc 1382) + 8192*(mc 2268 + mc 1383 - mc 1056*mc 1383 - 2*mc 2268*mc 1383 + 2*mc 2268*mc 1056*mc 1383) + 16384*(mc 2269 + mc 1384 - mc 993*mc 1384 - 2*mc 2269*mc 1384 + 2*mc 2269*mc 993*mc 1384) + 32768*(mc 2270 + mc 1385 - mc 994*mc 1385 - 2*mc 2270*mc 1385 + 2*mc 2270*mc 994*mc 1385)) - mc 2564 = 0 := by
  simp only [KeccakfPermAir.extraction.constraint_3009, KeccakfPermAir.extraction.inter_6839, hmc] at hx
  have e1 : KeccakfPermAir.extraction.inter_6838 c row = (mc 2256 + mc 1435 - mc 1044*mc 1435 - 2*mc 2256*mc 1435 + 2*mc 2256*mc 1044*mc 1435) + 2 * KeccakfPermAir.extraction.inter_6836 c row := by
    simp only [KeccakfPermAir.extraction.inter_6838, KeccakfPermAir.extraction.inter_6837, hmc]; ring
  have e2 : KeccakfPermAir.extraction.inter_6836 c row = (mc 2257 + mc 1436 - mc 1045*mc 1436 - 2*mc 2257*mc 1436 + 2*mc 2257*mc 1045*mc 1436) + 2 * KeccakfPermAir.extraction.inter_6834 c row := by
    simp only [KeccakfPermAir.extraction.inter_6836, KeccakfPermAir.extraction.inter_6835, hmc]; ring
  have e3 : KeccakfPermAir.extraction.inter_6834 c row = (mc 2258 + mc 1437 - mc 1046*mc 1437 - 2*mc 2258*mc 1437 + 2*mc 2258*mc 1046*mc 1437) + 2 * KeccakfPermAir.extraction.inter_6832 c row := by
    simp only [KeccakfPermAir.extraction.inter_6834, KeccakfPermAir.extraction.inter_6833, hmc]; ring
  have e4 : KeccakfPermAir.extraction.inter_6832 c row = (mc 2259 + mc 1438 - mc 1047*mc 1438 - 2*mc 2259*mc 1438 + 2*mc 2259*mc 1047*mc 1438) + 2 * KeccakfPermAir.extraction.inter_6830 c row := by
    simp only [KeccakfPermAir.extraction.inter_6832, KeccakfPermAir.extraction.inter_6831, hmc]; ring
  have e5 : KeccakfPermAir.extraction.inter_6830 c row = (mc 2260 + mc 1439 - mc 1048*mc 1439 - 2*mc 2260*mc 1439 + 2*mc 2260*mc 1048*mc 1439) + 2 * KeccakfPermAir.extraction.inter_6828 c row := by
    simp only [KeccakfPermAir.extraction.inter_6830, KeccakfPermAir.extraction.inter_6829, hmc]; ring
  have e6 : KeccakfPermAir.extraction.inter_6828 c row = (mc 2261 + mc 1440 - mc 1049*mc 1440 - 2*mc 2261*mc 1440 + 2*mc 2261*mc 1049*mc 1440) + 2 * KeccakfPermAir.extraction.inter_6826 c row := by
    simp only [KeccakfPermAir.extraction.inter_6828, KeccakfPermAir.extraction.inter_6827, hmc]; ring
  have e7 : KeccakfPermAir.extraction.inter_6826 c row = (mc 2262 + mc 1377 - mc 1050*mc 1377 - 2*mc 2262*mc 1377 + 2*mc 2262*mc 1050*mc 1377) + 2 * KeccakfPermAir.extraction.inter_6824 c row := by
    simp only [KeccakfPermAir.extraction.inter_6826, KeccakfPermAir.extraction.inter_6825, hmc]; ring
  have e8 : KeccakfPermAir.extraction.inter_6824 c row = (mc 2263 + mc 1378 - mc 1051*mc 1378 - 2*mc 2263*mc 1378 + 2*mc 2263*mc 1051*mc 1378) + 2 * KeccakfPermAir.extraction.inter_6822 c row := by
    simp only [KeccakfPermAir.extraction.inter_6824, KeccakfPermAir.extraction.inter_6823, hmc]; ring
  have e9 : KeccakfPermAir.extraction.inter_6822 c row = (mc 2264 + mc 1379 - mc 1052*mc 1379 - 2*mc 2264*mc 1379 + 2*mc 2264*mc 1052*mc 1379) + 2 * KeccakfPermAir.extraction.inter_6820 c row := by
    simp only [KeccakfPermAir.extraction.inter_6822, KeccakfPermAir.extraction.inter_6821, hmc]; ring
  have e10 : KeccakfPermAir.extraction.inter_6820 c row = (mc 2265 + mc 1380 - mc 1053*mc 1380 - 2*mc 2265*mc 1380 + 2*mc 2265*mc 1053*mc 1380) + 2 * KeccakfPermAir.extraction.inter_6818 c row := by
    simp only [KeccakfPermAir.extraction.inter_6820, KeccakfPermAir.extraction.inter_6819, hmc]; ring
  have e11 : KeccakfPermAir.extraction.inter_6818 c row = (mc 2266 + mc 1381 - mc 1054*mc 1381 - 2*mc 2266*mc 1381 + 2*mc 2266*mc 1054*mc 1381) + 2 * KeccakfPermAir.extraction.inter_6816 c row := by
    simp only [KeccakfPermAir.extraction.inter_6818, KeccakfPermAir.extraction.inter_6817, hmc]; ring
  have e12 : KeccakfPermAir.extraction.inter_6816 c row = (mc 2267 + mc 1382 - mc 1055*mc 1382 - 2*mc 2267*mc 1382 + 2*mc 2267*mc 1055*mc 1382) + 2 * KeccakfPermAir.extraction.inter_6814 c row := by
    simp only [KeccakfPermAir.extraction.inter_6816, KeccakfPermAir.extraction.inter_6815, hmc]; ring
  have e13 : KeccakfPermAir.extraction.inter_6814 c row = (mc 2268 + mc 1383 - mc 1056*mc 1383 - 2*mc 2268*mc 1383 + 2*mc 2268*mc 1056*mc 1383) + 2 * KeccakfPermAir.extraction.inter_6812 c row := by
    simp only [KeccakfPermAir.extraction.inter_6814, KeccakfPermAir.extraction.inter_6813, hmc]; ring
  have e14 : KeccakfPermAir.extraction.inter_6812 c row = (mc 2269 + mc 1384 - mc 993*mc 1384 - 2*mc 2269*mc 1384 + 2*mc 2269*mc 993*mc 1384) + 2 * KeccakfPermAir.extraction.inter_6810 c row := by
    simp only [KeccakfPermAir.extraction.inter_6812, KeccakfPermAir.extraction.inter_6811, hmc]; ring
  have e15 : KeccakfPermAir.extraction.inter_6810 c row = (mc 2270 + mc 1385 - mc 994*mc 1385 - 2*mc 2270*mc 1385 + 2*mc 2270*mc 994*mc 1385) := by
    simp only [KeccakfPermAir.extraction.inter_6810, KeccakfPermAir.extraction.inter_6809, hmc]; ring
  linear_combination hx - (2 : F) * e1 - (4 : F) * e2 - (8 : F) * e3 - (16 : F) * e4 - (32 : F) * e5 - (64 : F) * e6 - (128 : F) * e7 - (256 : F) * e8 - (512 : F) * e9 - (1024 : F) * e10 - (2048 : F) * e11 - (4096 : F) * e12 - (8192 : F) * e13 - (16384 : F) * e14 - (32768 : F) * e15

/-! ## Bridges: `ChiConstraints` field → `chiCanonicalK` for each limb -/

private theorem chi_bridge_0 (h : ChiConstraints air row) : chiCanonicalKProp air 0 row :=
  peel_chi_2910 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2910
private theorem chi_bridge_1 (h : ChiConstraints air row) : chiCanonicalKProp air 1 row :=
  peel_chi_2911 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2911
private theorem chi_bridge_2 (h : ChiConstraints air row) : chiCanonicalKProp air 2 row :=
  peel_chi_2912 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2912
private theorem chi_bridge_3 (h : ChiConstraints air row) : chiCanonicalKProp air 3 row :=
  peel_chi_2913 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2913
private theorem chi_bridge_4 (h : ChiConstraints air row) : chiCanonicalKProp air 4 row :=
  peel_chi_2914 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2914
private theorem chi_bridge_5 (h : ChiConstraints air row) : chiCanonicalKProp air 5 row :=
  peel_chi_2915 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2915
private theorem chi_bridge_6 (h : ChiConstraints air row) : chiCanonicalKProp air 6 row :=
  peel_chi_2916 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2916
private theorem chi_bridge_7 (h : ChiConstraints air row) : chiCanonicalKProp air 7 row :=
  peel_chi_2917 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2917
private theorem chi_bridge_8 (h : ChiConstraints air row) : chiCanonicalKProp air 8 row :=
  peel_chi_2918 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2918
private theorem chi_bridge_9 (h : ChiConstraints air row) : chiCanonicalKProp air 9 row :=
  peel_chi_2919 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2919
private theorem chi_bridge_10 (h : ChiConstraints air row) : chiCanonicalKProp air 10 row :=
  peel_chi_2920 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2920
private theorem chi_bridge_11 (h : ChiConstraints air row) : chiCanonicalKProp air 11 row :=
  peel_chi_2921 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2921
private theorem chi_bridge_12 (h : ChiConstraints air row) : chiCanonicalKProp air 12 row :=
  peel_chi_2922 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2922
private theorem chi_bridge_13 (h : ChiConstraints air row) : chiCanonicalKProp air 13 row :=
  peel_chi_2923 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2923
private theorem chi_bridge_14 (h : ChiConstraints air row) : chiCanonicalKProp air 14 row :=
  peel_chi_2924 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2924
private theorem chi_bridge_15 (h : ChiConstraints air row) : chiCanonicalKProp air 15 row :=
  peel_chi_2925 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2925
private theorem chi_bridge_16 (h : ChiConstraints air row) : chiCanonicalKProp air 16 row :=
  peel_chi_2926 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2926
private theorem chi_bridge_17 (h : ChiConstraints air row) : chiCanonicalKProp air 17 row :=
  peel_chi_2927 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2927
private theorem chi_bridge_18 (h : ChiConstraints air row) : chiCanonicalKProp air 18 row :=
  peel_chi_2928 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2928
private theorem chi_bridge_19 (h : ChiConstraints air row) : chiCanonicalKProp air 19 row :=
  peel_chi_2929 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2929
private theorem chi_bridge_20 (h : ChiConstraints air row) : chiCanonicalKProp air 20 row :=
  peel_chi_2930 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2930
private theorem chi_bridge_21 (h : ChiConstraints air row) : chiCanonicalKProp air 21 row :=
  peel_chi_2931 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2931
private theorem chi_bridge_22 (h : ChiConstraints air row) : chiCanonicalKProp air 22 row :=
  peel_chi_2932 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2932
private theorem chi_bridge_23 (h : ChiConstraints air row) : chiCanonicalKProp air 23 row :=
  peel_chi_2933 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2933
private theorem chi_bridge_24 (h : ChiConstraints air row) : chiCanonicalKProp air 24 row :=
  peel_chi_2934 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2934
private theorem chi_bridge_25 (h : ChiConstraints air row) : chiCanonicalKProp air 25 row :=
  peel_chi_2935 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2935
private theorem chi_bridge_26 (h : ChiConstraints air row) : chiCanonicalKProp air 26 row :=
  peel_chi_2936 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2936
private theorem chi_bridge_27 (h : ChiConstraints air row) : chiCanonicalKProp air 27 row :=
  peel_chi_2937 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2937
private theorem chi_bridge_28 (h : ChiConstraints air row) : chiCanonicalKProp air 28 row :=
  peel_chi_2938 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2938
private theorem chi_bridge_29 (h : ChiConstraints air row) : chiCanonicalKProp air 29 row :=
  peel_chi_2939 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2939
private theorem chi_bridge_30 (h : ChiConstraints air row) : chiCanonicalKProp air 30 row :=
  peel_chi_2940 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2940
private theorem chi_bridge_31 (h : ChiConstraints air row) : chiCanonicalKProp air 31 row :=
  peel_chi_2941 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2941
private theorem chi_bridge_32 (h : ChiConstraints air row) : chiCanonicalKProp air 32 row :=
  peel_chi_2942 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2942
private theorem chi_bridge_33 (h : ChiConstraints air row) : chiCanonicalKProp air 33 row :=
  peel_chi_2943 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2943
private theorem chi_bridge_34 (h : ChiConstraints air row) : chiCanonicalKProp air 34 row :=
  peel_chi_2944 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2944
private theorem chi_bridge_35 (h : ChiConstraints air row) : chiCanonicalKProp air 35 row :=
  peel_chi_2945 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2945
private theorem chi_bridge_36 (h : ChiConstraints air row) : chiCanonicalKProp air 36 row :=
  peel_chi_2946 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2946
private theorem chi_bridge_37 (h : ChiConstraints air row) : chiCanonicalKProp air 37 row :=
  peel_chi_2947 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2947
private theorem chi_bridge_38 (h : ChiConstraints air row) : chiCanonicalKProp air 38 row :=
  peel_chi_2948 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2948
private theorem chi_bridge_39 (h : ChiConstraints air row) : chiCanonicalKProp air 39 row :=
  peel_chi_2949 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2949
private theorem chi_bridge_40 (h : ChiConstraints air row) : chiCanonicalKProp air 40 row :=
  peel_chi_2950 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2950
private theorem chi_bridge_41 (h : ChiConstraints air row) : chiCanonicalKProp air 41 row :=
  peel_chi_2951 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2951
private theorem chi_bridge_42 (h : ChiConstraints air row) : chiCanonicalKProp air 42 row :=
  peel_chi_2952 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2952
private theorem chi_bridge_43 (h : ChiConstraints air row) : chiCanonicalKProp air 43 row :=
  peel_chi_2953 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2953
private theorem chi_bridge_44 (h : ChiConstraints air row) : chiCanonicalKProp air 44 row :=
  peel_chi_2954 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2954
private theorem chi_bridge_45 (h : ChiConstraints air row) : chiCanonicalKProp air 45 row :=
  peel_chi_2955 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2955
private theorem chi_bridge_46 (h : ChiConstraints air row) : chiCanonicalKProp air 46 row :=
  peel_chi_2956 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2956
private theorem chi_bridge_47 (h : ChiConstraints air row) : chiCanonicalKProp air 47 row :=
  peel_chi_2957 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2957
private theorem chi_bridge_48 (h : ChiConstraints air row) : chiCanonicalKProp air 48 row :=
  peel_chi_2958 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2958
private theorem chi_bridge_49 (h : ChiConstraints air row) : chiCanonicalKProp air 49 row :=
  peel_chi_2959 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2959
private theorem chi_bridge_50 (h : ChiConstraints air row) : chiCanonicalKProp air 50 row :=
  peel_chi_2960 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2960
private theorem chi_bridge_51 (h : ChiConstraints air row) : chiCanonicalKProp air 51 row :=
  peel_chi_2961 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2961
private theorem chi_bridge_52 (h : ChiConstraints air row) : chiCanonicalKProp air 52 row :=
  peel_chi_2962 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2962
private theorem chi_bridge_53 (h : ChiConstraints air row) : chiCanonicalKProp air 53 row :=
  peel_chi_2963 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2963
private theorem chi_bridge_54 (h : ChiConstraints air row) : chiCanonicalKProp air 54 row :=
  peel_chi_2964 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2964
private theorem chi_bridge_55 (h : ChiConstraints air row) : chiCanonicalKProp air 55 row :=
  peel_chi_2965 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2965
private theorem chi_bridge_56 (h : ChiConstraints air row) : chiCanonicalKProp air 56 row :=
  peel_chi_2966 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2966
private theorem chi_bridge_57 (h : ChiConstraints air row) : chiCanonicalKProp air 57 row :=
  peel_chi_2967 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2967
private theorem chi_bridge_58 (h : ChiConstraints air row) : chiCanonicalKProp air 58 row :=
  peel_chi_2968 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2968
private theorem chi_bridge_59 (h : ChiConstraints air row) : chiCanonicalKProp air 59 row :=
  peel_chi_2969 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2969
private theorem chi_bridge_60 (h : ChiConstraints air row) : chiCanonicalKProp air 60 row :=
  peel_chi_2970 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2970
private theorem chi_bridge_61 (h : ChiConstraints air row) : chiCanonicalKProp air 61 row :=
  peel_chi_2971 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2971
private theorem chi_bridge_62 (h : ChiConstraints air row) : chiCanonicalKProp air 62 row :=
  peel_chi_2972 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2972
private theorem chi_bridge_63 (h : ChiConstraints air row) : chiCanonicalKProp air 63 row :=
  peel_chi_2973 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2973
private theorem chi_bridge_64 (h : ChiConstraints air row) : chiCanonicalKProp air 64 row :=
  peel_chi_2974 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2974
private theorem chi_bridge_65 (h : ChiConstraints air row) : chiCanonicalKProp air 65 row :=
  peel_chi_2975 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2975
private theorem chi_bridge_66 (h : ChiConstraints air row) : chiCanonicalKProp air 66 row :=
  peel_chi_2976 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2976
private theorem chi_bridge_67 (h : ChiConstraints air row) : chiCanonicalKProp air 67 row :=
  peel_chi_2977 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2977
private theorem chi_bridge_68 (h : ChiConstraints air row) : chiCanonicalKProp air 68 row :=
  peel_chi_2978 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2978
private theorem chi_bridge_69 (h : ChiConstraints air row) : chiCanonicalKProp air 69 row :=
  peel_chi_2979 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2979
private theorem chi_bridge_70 (h : ChiConstraints air row) : chiCanonicalKProp air 70 row :=
  peel_chi_2980 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2980
private theorem chi_bridge_71 (h : ChiConstraints air row) : chiCanonicalKProp air 71 row :=
  peel_chi_2981 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2981
private theorem chi_bridge_72 (h : ChiConstraints air row) : chiCanonicalKProp air 72 row :=
  peel_chi_2982 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2982
private theorem chi_bridge_73 (h : ChiConstraints air row) : chiCanonicalKProp air 73 row :=
  peel_chi_2983 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2983
private theorem chi_bridge_74 (h : ChiConstraints air row) : chiCanonicalKProp air 74 row :=
  peel_chi_2984 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2984
private theorem chi_bridge_75 (h : ChiConstraints air row) : chiCanonicalKProp air 75 row :=
  peel_chi_2985 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2985
private theorem chi_bridge_76 (h : ChiConstraints air row) : chiCanonicalKProp air 76 row :=
  peel_chi_2986 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2986
private theorem chi_bridge_77 (h : ChiConstraints air row) : chiCanonicalKProp air 77 row :=
  peel_chi_2987 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2987
private theorem chi_bridge_78 (h : ChiConstraints air row) : chiCanonicalKProp air 78 row :=
  peel_chi_2988 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2988
private theorem chi_bridge_79 (h : ChiConstraints air row) : chiCanonicalKProp air 79 row :=
  peel_chi_2989 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2989
private theorem chi_bridge_80 (h : ChiConstraints air row) : chiCanonicalKProp air 80 row :=
  peel_chi_2990 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2990
private theorem chi_bridge_81 (h : ChiConstraints air row) : chiCanonicalKProp air 81 row :=
  peel_chi_2991 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2991
private theorem chi_bridge_82 (h : ChiConstraints air row) : chiCanonicalKProp air 82 row :=
  peel_chi_2992 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2992
private theorem chi_bridge_83 (h : ChiConstraints air row) : chiCanonicalKProp air 83 row :=
  peel_chi_2993 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2993
private theorem chi_bridge_84 (h : ChiConstraints air row) : chiCanonicalKProp air 84 row :=
  peel_chi_2994 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2994
private theorem chi_bridge_85 (h : ChiConstraints air row) : chiCanonicalKProp air 85 row :=
  peel_chi_2995 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2995
private theorem chi_bridge_86 (h : ChiConstraints air row) : chiCanonicalKProp air 86 row :=
  peel_chi_2996 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2996
private theorem chi_bridge_87 (h : ChiConstraints air row) : chiCanonicalKProp air 87 row :=
  peel_chi_2997 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2997
private theorem chi_bridge_88 (h : ChiConstraints air row) : chiCanonicalKProp air 88 row :=
  peel_chi_2998 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2998
private theorem chi_bridge_89 (h : ChiConstraints air row) : chiCanonicalKProp air 89 row :=
  peel_chi_2999 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h2999
private theorem chi_bridge_90 (h : ChiConstraints air row) : chiCanonicalKProp air 90 row :=
  peel_chi_3000 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h3000
private theorem chi_bridge_91 (h : ChiConstraints air row) : chiCanonicalKProp air 91 row :=
  peel_chi_3001 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h3001
private theorem chi_bridge_92 (h : ChiConstraints air row) : chiCanonicalKProp air 92 row :=
  peel_chi_3002 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h3002
private theorem chi_bridge_93 (h : ChiConstraints air row) : chiCanonicalKProp air 93 row :=
  peel_chi_3003 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h3003
private theorem chi_bridge_94 (h : ChiConstraints air row) : chiCanonicalKProp air 94 row :=
  peel_chi_3004 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h3004
private theorem chi_bridge_95 (h : ChiConstraints air row) : chiCanonicalKProp air 95 row :=
  peel_chi_3005 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h3005
private theorem chi_bridge_96 (h : ChiConstraints air row) : chiCanonicalKProp air 96 row :=
  peel_chi_3006 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h3006
private theorem chi_bridge_97 (h : ChiConstraints air row) : chiCanonicalKProp air 97 row :=
  peel_chi_3007 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h3007
private theorem chi_bridge_98 (h : ChiConstraints air row) : chiCanonicalKProp air 98 row :=
  peel_chi_3008 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h3008
private theorem chi_bridge_99 (h : ChiConstraints air row) : chiCanonicalKProp air 99 row :=
  peel_chi_3009 air (fun col => Circuit.main air (id := 0) (column := col) (row := row) (rotation := 0)) (fun _ => rfl) h.h3009

/-- Bridge the bundled `ChiConstraints` to `chiCanonicalK air n row` for any
    `n : Fin 100`, dispatching on the concrete limb index.  Returns the folded
    `chiCanonicalKProp` so the generated dependent matcher stays small; the
    result type is definitionally `chiCanonicalK air n.val row`. -/
noncomputable def chi_canonical_of_chi
    (h : ChiConstraints air row) (n : Fin 100) : chiCanonicalK air n.val row :=
  (match n with
   | ⟨0, _⟩ => chi_bridge_0 h
   | ⟨1, _⟩ => chi_bridge_1 h
   | ⟨2, _⟩ => chi_bridge_2 h
   | ⟨3, _⟩ => chi_bridge_3 h
   | ⟨4, _⟩ => chi_bridge_4 h
   | ⟨5, _⟩ => chi_bridge_5 h
   | ⟨6, _⟩ => chi_bridge_6 h
   | ⟨7, _⟩ => chi_bridge_7 h
   | ⟨8, _⟩ => chi_bridge_8 h
   | ⟨9, _⟩ => chi_bridge_9 h
   | ⟨10, _⟩ => chi_bridge_10 h
   | ⟨11, _⟩ => chi_bridge_11 h
   | ⟨12, _⟩ => chi_bridge_12 h
   | ⟨13, _⟩ => chi_bridge_13 h
   | ⟨14, _⟩ => chi_bridge_14 h
   | ⟨15, _⟩ => chi_bridge_15 h
   | ⟨16, _⟩ => chi_bridge_16 h
   | ⟨17, _⟩ => chi_bridge_17 h
   | ⟨18, _⟩ => chi_bridge_18 h
   | ⟨19, _⟩ => chi_bridge_19 h
   | ⟨20, _⟩ => chi_bridge_20 h
   | ⟨21, _⟩ => chi_bridge_21 h
   | ⟨22, _⟩ => chi_bridge_22 h
   | ⟨23, _⟩ => chi_bridge_23 h
   | ⟨24, _⟩ => chi_bridge_24 h
   | ⟨25, _⟩ => chi_bridge_25 h
   | ⟨26, _⟩ => chi_bridge_26 h
   | ⟨27, _⟩ => chi_bridge_27 h
   | ⟨28, _⟩ => chi_bridge_28 h
   | ⟨29, _⟩ => chi_bridge_29 h
   | ⟨30, _⟩ => chi_bridge_30 h
   | ⟨31, _⟩ => chi_bridge_31 h
   | ⟨32, _⟩ => chi_bridge_32 h
   | ⟨33, _⟩ => chi_bridge_33 h
   | ⟨34, _⟩ => chi_bridge_34 h
   | ⟨35, _⟩ => chi_bridge_35 h
   | ⟨36, _⟩ => chi_bridge_36 h
   | ⟨37, _⟩ => chi_bridge_37 h
   | ⟨38, _⟩ => chi_bridge_38 h
   | ⟨39, _⟩ => chi_bridge_39 h
   | ⟨40, _⟩ => chi_bridge_40 h
   | ⟨41, _⟩ => chi_bridge_41 h
   | ⟨42, _⟩ => chi_bridge_42 h
   | ⟨43, _⟩ => chi_bridge_43 h
   | ⟨44, _⟩ => chi_bridge_44 h
   | ⟨45, _⟩ => chi_bridge_45 h
   | ⟨46, _⟩ => chi_bridge_46 h
   | ⟨47, _⟩ => chi_bridge_47 h
   | ⟨48, _⟩ => chi_bridge_48 h
   | ⟨49, _⟩ => chi_bridge_49 h
   | ⟨50, _⟩ => chi_bridge_50 h
   | ⟨51, _⟩ => chi_bridge_51 h
   | ⟨52, _⟩ => chi_bridge_52 h
   | ⟨53, _⟩ => chi_bridge_53 h
   | ⟨54, _⟩ => chi_bridge_54 h
   | ⟨55, _⟩ => chi_bridge_55 h
   | ⟨56, _⟩ => chi_bridge_56 h
   | ⟨57, _⟩ => chi_bridge_57 h
   | ⟨58, _⟩ => chi_bridge_58 h
   | ⟨59, _⟩ => chi_bridge_59 h
   | ⟨60, _⟩ => chi_bridge_60 h
   | ⟨61, _⟩ => chi_bridge_61 h
   | ⟨62, _⟩ => chi_bridge_62 h
   | ⟨63, _⟩ => chi_bridge_63 h
   | ⟨64, _⟩ => chi_bridge_64 h
   | ⟨65, _⟩ => chi_bridge_65 h
   | ⟨66, _⟩ => chi_bridge_66 h
   | ⟨67, _⟩ => chi_bridge_67 h
   | ⟨68, _⟩ => chi_bridge_68 h
   | ⟨69, _⟩ => chi_bridge_69 h
   | ⟨70, _⟩ => chi_bridge_70 h
   | ⟨71, _⟩ => chi_bridge_71 h
   | ⟨72, _⟩ => chi_bridge_72 h
   | ⟨73, _⟩ => chi_bridge_73 h
   | ⟨74, _⟩ => chi_bridge_74 h
   | ⟨75, _⟩ => chi_bridge_75 h
   | ⟨76, _⟩ => chi_bridge_76 h
   | ⟨77, _⟩ => chi_bridge_77 h
   | ⟨78, _⟩ => chi_bridge_78 h
   | ⟨79, _⟩ => chi_bridge_79 h
   | ⟨80, _⟩ => chi_bridge_80 h
   | ⟨81, _⟩ => chi_bridge_81 h
   | ⟨82, _⟩ => chi_bridge_82 h
   | ⟨83, _⟩ => chi_bridge_83 h
   | ⟨84, _⟩ => chi_bridge_84 h
   | ⟨85, _⟩ => chi_bridge_85 h
   | ⟨86, _⟩ => chi_bridge_86 h
   | ⟨87, _⟩ => chi_bridge_87 h
   | ⟨88, _⟩ => chi_bridge_88 h
   | ⟨89, _⟩ => chi_bridge_89 h
   | ⟨90, _⟩ => chi_bridge_90 h
   | ⟨91, _⟩ => chi_bridge_91 h
   | ⟨92, _⟩ => chi_bridge_92 h
   | ⟨93, _⟩ => chi_bridge_93 h
   | ⟨94, _⟩ => chi_bridge_94 h
   | ⟨95, _⟩ => chi_bridge_95 h
   | ⟨96, _⟩ => chi_bridge_96 h
   | ⟨97, _⟩ => chi_bridge_97 h
   | ⟨98, _⟩ => chi_bridge_98 h
   | ⟨99, _⟩ => chi_bridge_99 h
   | ⟨n + 100, hn⟩ => absurd hn (by omega) : chiCanonicalKProp air n.val row)

end KeccakfPermAir.Soundness

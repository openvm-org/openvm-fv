import VmExtensions.Constraints.KeccakfPermAir.AllHoldSplit
import VmExtensions.Soundness.KeccakfPermAir.Round.Surface
import OpenvmFv.Fundamentals.BabyBear

set_option autoImplicit false
set_option linter.unusedVariables false

namespace KeccakfPermAir.Soundness

open KeccakfPermAir.constraints
open BabyBear

/-!
  ## RoundLocalConstraints extraction from seg_E
-/

-- Control header (2 items)
def seg_E_header
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_248 c row,
    constraint_249 c row
  ]

-- CBits boolean (320 items)
def seg_E_cbits
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_250 c row,
    constraint_251 c row,
    constraint_252 c row,
    constraint_253 c row,
    constraint_254 c row,
    constraint_255 c row,
    constraint_256 c row,
    constraint_257 c row,
    constraint_258 c row,
    constraint_259 c row,
    constraint_260 c row,
    constraint_261 c row,
    constraint_262 c row,
    constraint_263 c row,
    constraint_264 c row,
    constraint_265 c row,
    constraint_266 c row,
    constraint_267 c row,
    constraint_268 c row,
    constraint_269 c row,
    constraint_270 c row,
    constraint_271 c row,
    constraint_272 c row,
    constraint_273 c row,
    constraint_274 c row,
    constraint_275 c row,
    constraint_276 c row,
    constraint_277 c row,
    constraint_278 c row,
    constraint_279 c row,
    constraint_280 c row,
    constraint_281 c row,
    constraint_282 c row,
    constraint_283 c row,
    constraint_284 c row,
    constraint_285 c row,
    constraint_286 c row,
    constraint_287 c row,
    constraint_288 c row,
    constraint_289 c row,
    constraint_290 c row,
    constraint_291 c row,
    constraint_292 c row,
    constraint_293 c row,
    constraint_294 c row,
    constraint_295 c row,
    constraint_296 c row,
    constraint_297 c row,
    constraint_298 c row,
    constraint_299 c row,
    constraint_300 c row,
    constraint_301 c row,
    constraint_302 c row,
    constraint_303 c row,
    constraint_304 c row,
    constraint_305 c row,
    constraint_306 c row,
    constraint_307 c row,
    constraint_308 c row,
    constraint_309 c row,
    constraint_310 c row,
    constraint_311 c row,
    constraint_312 c row,
    constraint_313 c row,
    constraint_314 c row,
    constraint_315 c row,
    constraint_316 c row,
    constraint_317 c row,
    constraint_318 c row,
    constraint_319 c row,
    constraint_320 c row,
    constraint_321 c row,
    constraint_322 c row,
    constraint_323 c row,
    constraint_324 c row,
    constraint_325 c row,
    constraint_326 c row,
    constraint_327 c row,
    constraint_328 c row,
    constraint_329 c row,
    constraint_330 c row,
    constraint_331 c row,
    constraint_332 c row,
    constraint_333 c row,
    constraint_334 c row,
    constraint_335 c row,
    constraint_336 c row,
    constraint_337 c row,
    constraint_338 c row,
    constraint_339 c row,
    constraint_340 c row,
    constraint_341 c row,
    constraint_342 c row,
    constraint_343 c row,
    constraint_344 c row,
    constraint_345 c row,
    constraint_346 c row,
    constraint_347 c row,
    constraint_348 c row,
    constraint_349 c row,
    constraint_350 c row,
    constraint_351 c row,
    constraint_352 c row,
    constraint_353 c row,
    constraint_354 c row,
    constraint_355 c row,
    constraint_356 c row,
    constraint_357 c row,
    constraint_358 c row,
    constraint_359 c row,
    constraint_360 c row,
    constraint_361 c row,
    constraint_362 c row,
    constraint_363 c row,
    constraint_364 c row,
    constraint_365 c row,
    constraint_366 c row,
    constraint_367 c row,
    constraint_368 c row,
    constraint_369 c row,
    constraint_370 c row,
    constraint_371 c row,
    constraint_372 c row,
    constraint_373 c row,
    constraint_374 c row,
    constraint_375 c row,
    constraint_376 c row,
    constraint_377 c row,
    constraint_378 c row,
    constraint_379 c row,
    constraint_380 c row,
    constraint_381 c row,
    constraint_382 c row,
    constraint_383 c row,
    constraint_384 c row,
    constraint_385 c row,
    constraint_386 c row,
    constraint_387 c row,
    constraint_388 c row,
    constraint_389 c row,
    constraint_390 c row,
    constraint_391 c row,
    constraint_392 c row,
    constraint_393 c row,
    constraint_394 c row,
    constraint_395 c row,
    constraint_396 c row,
    constraint_397 c row,
    constraint_398 c row,
    constraint_399 c row,
    constraint_400 c row,
    constraint_401 c row,
    constraint_402 c row,
    constraint_403 c row,
    constraint_404 c row,
    constraint_405 c row,
    constraint_406 c row,
    constraint_407 c row,
    constraint_408 c row,
    constraint_409 c row,
    constraint_410 c row,
    constraint_411 c row,
    constraint_412 c row,
    constraint_413 c row,
    constraint_414 c row,
    constraint_415 c row,
    constraint_416 c row,
    constraint_417 c row,
    constraint_418 c row,
    constraint_419 c row,
    constraint_420 c row,
    constraint_421 c row,
    constraint_422 c row,
    constraint_423 c row,
    constraint_424 c row,
    constraint_425 c row,
    constraint_426 c row,
    constraint_427 c row,
    constraint_428 c row,
    constraint_429 c row,
    constraint_430 c row,
    constraint_431 c row,
    constraint_432 c row,
    constraint_433 c row,
    constraint_434 c row,
    constraint_435 c row,
    constraint_436 c row,
    constraint_437 c row,
    constraint_438 c row,
    constraint_439 c row,
    constraint_440 c row,
    constraint_441 c row,
    constraint_442 c row,
    constraint_443 c row,
    constraint_444 c row,
    constraint_445 c row,
    constraint_446 c row,
    constraint_447 c row,
    constraint_448 c row,
    constraint_449 c row,
    constraint_450 c row,
    constraint_451 c row,
    constraint_452 c row,
    constraint_453 c row,
    constraint_454 c row,
    constraint_455 c row,
    constraint_456 c row,
    constraint_457 c row,
    constraint_458 c row,
    constraint_459 c row,
    constraint_460 c row,
    constraint_461 c row,
    constraint_462 c row,
    constraint_463 c row,
    constraint_464 c row,
    constraint_465 c row,
    constraint_466 c row,
    constraint_467 c row,
    constraint_468 c row,
    constraint_469 c row,
    constraint_470 c row,
    constraint_471 c row,
    constraint_472 c row,
    constraint_473 c row,
    constraint_474 c row,
    constraint_475 c row,
    constraint_476 c row,
    constraint_477 c row,
    constraint_478 c row,
    constraint_479 c row,
    constraint_480 c row,
    constraint_481 c row,
    constraint_482 c row,
    constraint_483 c row,
    constraint_484 c row,
    constraint_485 c row,
    constraint_486 c row,
    constraint_487 c row,
    constraint_488 c row,
    constraint_489 c row,
    constraint_490 c row,
    constraint_491 c row,
    constraint_492 c row,
    constraint_493 c row,
    constraint_494 c row,
    constraint_495 c row,
    constraint_496 c row,
    constraint_497 c row,
    constraint_498 c row,
    constraint_499 c row,
    constraint_500 c row,
    constraint_501 c row,
    constraint_502 c row,
    constraint_503 c row,
    constraint_504 c row,
    constraint_505 c row,
    constraint_506 c row,
    constraint_507 c row,
    constraint_508 c row,
    constraint_509 c row,
    constraint_510 c row,
    constraint_511 c row,
    constraint_512 c row,
    constraint_513 c row,
    constraint_514 c row,
    constraint_515 c row,
    constraint_516 c row,
    constraint_517 c row,
    constraint_518 c row,
    constraint_519 c row,
    constraint_520 c row,
    constraint_521 c row,
    constraint_522 c row,
    constraint_523 c row,
    constraint_524 c row,
    constraint_525 c row,
    constraint_526 c row,
    constraint_527 c row,
    constraint_528 c row,
    constraint_529 c row,
    constraint_530 c row,
    constraint_531 c row,
    constraint_532 c row,
    constraint_533 c row,
    constraint_534 c row,
    constraint_535 c row,
    constraint_536 c row,
    constraint_537 c row,
    constraint_538 c row,
    constraint_539 c row,
    constraint_540 c row,
    constraint_541 c row,
    constraint_542 c row,
    constraint_543 c row,
    constraint_544 c row,
    constraint_545 c row,
    constraint_546 c row,
    constraint_547 c row,
    constraint_548 c row,
    constraint_549 c row,
    constraint_550 c row,
    constraint_551 c row,
    constraint_552 c row,
    constraint_553 c row,
    constraint_554 c row,
    constraint_555 c row,
    constraint_556 c row,
    constraint_557 c row,
    constraint_558 c row,
    constraint_559 c row,
    constraint_560 c row,
    constraint_561 c row,
    constraint_562 c row,
    constraint_563 c row,
    constraint_564 c row,
    constraint_565 c row,
    constraint_566 c row,
    constraint_567 c row,
    constraint_568 c row,
    constraint_569 c row
  ]

-- CPrime XOR (320 items)
def seg_E_cprime
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_570 c row,
    constraint_571 c row,
    constraint_572 c row,
    constraint_573 c row,
    constraint_574 c row,
    constraint_575 c row,
    constraint_576 c row,
    constraint_577 c row,
    constraint_578 c row,
    constraint_579 c row,
    constraint_580 c row,
    constraint_581 c row,
    constraint_582 c row,
    constraint_583 c row,
    constraint_584 c row,
    constraint_585 c row,
    constraint_586 c row,
    constraint_587 c row,
    constraint_588 c row,
    constraint_589 c row,
    constraint_590 c row,
    constraint_591 c row,
    constraint_592 c row,
    constraint_593 c row,
    constraint_594 c row,
    constraint_595 c row,
    constraint_596 c row,
    constraint_597 c row,
    constraint_598 c row,
    constraint_599 c row,
    constraint_600 c row,
    constraint_601 c row,
    constraint_602 c row,
    constraint_603 c row,
    constraint_604 c row,
    constraint_605 c row,
    constraint_606 c row,
    constraint_607 c row,
    constraint_608 c row,
    constraint_609 c row,
    constraint_610 c row,
    constraint_611 c row,
    constraint_612 c row,
    constraint_613 c row,
    constraint_614 c row,
    constraint_615 c row,
    constraint_616 c row,
    constraint_617 c row,
    constraint_618 c row,
    constraint_619 c row,
    constraint_620 c row,
    constraint_621 c row,
    constraint_622 c row,
    constraint_623 c row,
    constraint_624 c row,
    constraint_625 c row,
    constraint_626 c row,
    constraint_627 c row,
    constraint_628 c row,
    constraint_629 c row,
    constraint_630 c row,
    constraint_631 c row,
    constraint_632 c row,
    constraint_633 c row,
    constraint_634 c row,
    constraint_635 c row,
    constraint_636 c row,
    constraint_637 c row,
    constraint_638 c row,
    constraint_639 c row,
    constraint_640 c row,
    constraint_641 c row,
    constraint_642 c row,
    constraint_643 c row,
    constraint_644 c row,
    constraint_645 c row,
    constraint_646 c row,
    constraint_647 c row,
    constraint_648 c row,
    constraint_649 c row,
    constraint_650 c row,
    constraint_651 c row,
    constraint_652 c row,
    constraint_653 c row,
    constraint_654 c row,
    constraint_655 c row,
    constraint_656 c row,
    constraint_657 c row,
    constraint_658 c row,
    constraint_659 c row,
    constraint_660 c row,
    constraint_661 c row,
    constraint_662 c row,
    constraint_663 c row,
    constraint_664 c row,
    constraint_665 c row,
    constraint_666 c row,
    constraint_667 c row,
    constraint_668 c row,
    constraint_669 c row,
    constraint_670 c row,
    constraint_671 c row,
    constraint_672 c row,
    constraint_673 c row,
    constraint_674 c row,
    constraint_675 c row,
    constraint_676 c row,
    constraint_677 c row,
    constraint_678 c row,
    constraint_679 c row,
    constraint_680 c row,
    constraint_681 c row,
    constraint_682 c row,
    constraint_683 c row,
    constraint_684 c row,
    constraint_685 c row,
    constraint_686 c row,
    constraint_687 c row,
    constraint_688 c row,
    constraint_689 c row,
    constraint_690 c row,
    constraint_691 c row,
    constraint_692 c row,
    constraint_693 c row,
    constraint_694 c row,
    constraint_695 c row,
    constraint_696 c row,
    constraint_697 c row,
    constraint_698 c row,
    constraint_699 c row,
    constraint_700 c row,
    constraint_701 c row,
    constraint_702 c row,
    constraint_703 c row,
    constraint_704 c row,
    constraint_705 c row,
    constraint_706 c row,
    constraint_707 c row,
    constraint_708 c row,
    constraint_709 c row,
    constraint_710 c row,
    constraint_711 c row,
    constraint_712 c row,
    constraint_713 c row,
    constraint_714 c row,
    constraint_715 c row,
    constraint_716 c row,
    constraint_717 c row,
    constraint_718 c row,
    constraint_719 c row,
    constraint_720 c row,
    constraint_721 c row,
    constraint_722 c row,
    constraint_723 c row,
    constraint_724 c row,
    constraint_725 c row,
    constraint_726 c row,
    constraint_727 c row,
    constraint_728 c row,
    constraint_729 c row,
    constraint_730 c row,
    constraint_731 c row,
    constraint_732 c row,
    constraint_733 c row,
    constraint_734 c row,
    constraint_735 c row,
    constraint_736 c row,
    constraint_737 c row,
    constraint_738 c row,
    constraint_739 c row,
    constraint_740 c row,
    constraint_741 c row,
    constraint_742 c row,
    constraint_743 c row,
    constraint_744 c row,
    constraint_745 c row,
    constraint_746 c row,
    constraint_747 c row,
    constraint_748 c row,
    constraint_749 c row,
    constraint_750 c row,
    constraint_751 c row,
    constraint_752 c row,
    constraint_753 c row,
    constraint_754 c row,
    constraint_755 c row,
    constraint_756 c row,
    constraint_757 c row,
    constraint_758 c row,
    constraint_759 c row,
    constraint_760 c row,
    constraint_761 c row,
    constraint_762 c row,
    constraint_763 c row,
    constraint_764 c row,
    constraint_765 c row,
    constraint_766 c row,
    constraint_767 c row,
    constraint_768 c row,
    constraint_769 c row,
    constraint_770 c row,
    constraint_771 c row,
    constraint_772 c row,
    constraint_773 c row,
    constraint_774 c row,
    constraint_775 c row,
    constraint_776 c row,
    constraint_777 c row,
    constraint_778 c row,
    constraint_779 c row,
    constraint_780 c row,
    constraint_781 c row,
    constraint_782 c row,
    constraint_783 c row,
    constraint_784 c row,
    constraint_785 c row,
    constraint_786 c row,
    constraint_787 c row,
    constraint_788 c row,
    constraint_789 c row,
    constraint_790 c row,
    constraint_791 c row,
    constraint_792 c row,
    constraint_793 c row,
    constraint_794 c row,
    constraint_795 c row,
    constraint_796 c row,
    constraint_797 c row,
    constraint_798 c row,
    constraint_799 c row,
    constraint_800 c row,
    constraint_801 c row,
    constraint_802 c row,
    constraint_803 c row,
    constraint_804 c row,
    constraint_805 c row,
    constraint_806 c row,
    constraint_807 c row,
    constraint_808 c row,
    constraint_809 c row,
    constraint_810 c row,
    constraint_811 c row,
    constraint_812 c row,
    constraint_813 c row,
    constraint_814 c row,
    constraint_815 c row,
    constraint_816 c row,
    constraint_817 c row,
    constraint_818 c row,
    constraint_819 c row,
    constraint_820 c row,
    constraint_821 c row,
    constraint_822 c row,
    constraint_823 c row,
    constraint_824 c row,
    constraint_825 c row,
    constraint_826 c row,
    constraint_827 c row,
    constraint_828 c row,
    constraint_829 c row,
    constraint_830 c row,
    constraint_831 c row,
    constraint_832 c row,
    constraint_833 c row,
    constraint_834 c row,
    constraint_835 c row,
    constraint_836 c row,
    constraint_837 c row,
    constraint_838 c row,
    constraint_839 c row,
    constraint_840 c row,
    constraint_841 c row,
    constraint_842 c row,
    constraint_843 c row,
    constraint_844 c row,
    constraint_845 c row,
    constraint_846 c row,
    constraint_847 c row,
    constraint_848 c row,
    constraint_849 c row,
    constraint_850 c row,
    constraint_851 c row,
    constraint_852 c row,
    constraint_853 c row,
    constraint_854 c row,
    constraint_855 c row,
    constraint_856 c row,
    constraint_857 c row,
    constraint_858 c row,
    constraint_859 c row,
    constraint_860 c row,
    constraint_861 c row,
    constraint_862 c row,
    constraint_863 c row,
    constraint_864 c row,
    constraint_865 c row,
    constraint_866 c row,
    constraint_867 c row,
    constraint_868 c row,
    constraint_869 c row,
    constraint_870 c row,
    constraint_871 c row,
    constraint_872 c row,
    constraint_873 c row,
    constraint_874 c row,
    constraint_875 c row,
    constraint_876 c row,
    constraint_877 c row,
    constraint_878 c row,
    constraint_879 c row,
    constraint_880 c row,
    constraint_881 c row,
    constraint_882 c row,
    constraint_883 c row,
    constraint_884 c row,
    constraint_885 c row,
    constraint_886 c row,
    constraint_887 c row,
    constraint_888 c row,
    constraint_889 c row
  ]

-- APrime group 0 (340 items)
def seg_E_ap_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_890 c row,
    constraint_891 c row,
    constraint_892 c row,
    constraint_893 c row,
    constraint_894 c row,
    constraint_895 c row,
    constraint_896 c row,
    constraint_897 c row,
    constraint_898 c row,
    constraint_899 c row,
    constraint_900 c row,
    constraint_901 c row,
    constraint_902 c row,
    constraint_903 c row,
    constraint_904 c row,
    constraint_905 c row,
    constraint_906 c row,
    constraint_907 c row,
    constraint_908 c row,
    constraint_909 c row,
    constraint_910 c row,
    constraint_911 c row,
    constraint_912 c row,
    constraint_913 c row,
    constraint_914 c row,
    constraint_915 c row,
    constraint_916 c row,
    constraint_917 c row,
    constraint_918 c row,
    constraint_919 c row,
    constraint_920 c row,
    constraint_921 c row,
    constraint_922 c row,
    constraint_923 c row,
    constraint_924 c row,
    constraint_925 c row,
    constraint_926 c row,
    constraint_927 c row,
    constraint_928 c row,
    constraint_929 c row,
    constraint_930 c row,
    constraint_931 c row,
    constraint_932 c row,
    constraint_933 c row,
    constraint_934 c row,
    constraint_935 c row,
    constraint_936 c row,
    constraint_937 c row,
    constraint_938 c row,
    constraint_939 c row,
    constraint_940 c row,
    constraint_941 c row,
    constraint_942 c row,
    constraint_943 c row,
    constraint_944 c row,
    constraint_945 c row,
    constraint_946 c row,
    constraint_947 c row,
    constraint_948 c row,
    constraint_949 c row,
    constraint_950 c row,
    constraint_951 c row,
    constraint_952 c row,
    constraint_953 c row,
    constraint_954 c row,
    constraint_955 c row,
    constraint_956 c row,
    constraint_957 c row,
    constraint_958 c row,
    constraint_959 c row,
    constraint_960 c row,
    constraint_961 c row,
    constraint_962 c row,
    constraint_963 c row,
    constraint_964 c row,
    constraint_965 c row,
    constraint_966 c row,
    constraint_967 c row,
    constraint_968 c row,
    constraint_969 c row,
    constraint_970 c row,
    constraint_971 c row,
    constraint_972 c row,
    constraint_973 c row,
    constraint_974 c row,
    constraint_975 c row,
    constraint_976 c row,
    constraint_977 c row,
    constraint_978 c row,
    constraint_979 c row,
    constraint_980 c row,
    constraint_981 c row,
    constraint_982 c row,
    constraint_983 c row,
    constraint_984 c row,
    constraint_985 c row,
    constraint_986 c row,
    constraint_987 c row,
    constraint_988 c row,
    constraint_989 c row,
    constraint_990 c row,
    constraint_991 c row,
    constraint_992 c row,
    constraint_993 c row,
    constraint_994 c row,
    constraint_995 c row,
    constraint_996 c row,
    constraint_997 c row,
    constraint_998 c row,
    constraint_999 c row,
    constraint_1000 c row,
    constraint_1001 c row,
    constraint_1002 c row,
    constraint_1003 c row,
    constraint_1004 c row,
    constraint_1005 c row,
    constraint_1006 c row,
    constraint_1007 c row,
    constraint_1008 c row,
    constraint_1009 c row,
    constraint_1010 c row,
    constraint_1011 c row,
    constraint_1012 c row,
    constraint_1013 c row,
    constraint_1014 c row,
    constraint_1015 c row,
    constraint_1016 c row,
    constraint_1017 c row,
    constraint_1018 c row,
    constraint_1019 c row,
    constraint_1020 c row,
    constraint_1021 c row,
    constraint_1022 c row,
    constraint_1023 c row,
    constraint_1024 c row,
    constraint_1025 c row,
    constraint_1026 c row,
    constraint_1027 c row,
    constraint_1028 c row,
    constraint_1029 c row,
    constraint_1030 c row,
    constraint_1031 c row,
    constraint_1032 c row,
    constraint_1033 c row,
    constraint_1034 c row,
    constraint_1035 c row,
    constraint_1036 c row,
    constraint_1037 c row,
    constraint_1038 c row,
    constraint_1039 c row,
    constraint_1040 c row,
    constraint_1041 c row,
    constraint_1042 c row,
    constraint_1043 c row,
    constraint_1044 c row,
    constraint_1045 c row,
    constraint_1046 c row,
    constraint_1047 c row,
    constraint_1048 c row,
    constraint_1049 c row,
    constraint_1050 c row,
    constraint_1051 c row,
    constraint_1052 c row,
    constraint_1053 c row,
    constraint_1054 c row,
    constraint_1055 c row,
    constraint_1056 c row,
    constraint_1057 c row,
    constraint_1058 c row,
    constraint_1059 c row,
    constraint_1060 c row,
    constraint_1061 c row,
    constraint_1062 c row,
    constraint_1063 c row,
    constraint_1064 c row,
    constraint_1065 c row,
    constraint_1066 c row,
    constraint_1067 c row,
    constraint_1068 c row,
    constraint_1069 c row,
    constraint_1070 c row,
    constraint_1071 c row,
    constraint_1072 c row,
    constraint_1073 c row,
    constraint_1074 c row,
    constraint_1075 c row,
    constraint_1076 c row,
    constraint_1077 c row,
    constraint_1078 c row,
    constraint_1079 c row,
    constraint_1080 c row,
    constraint_1081 c row,
    constraint_1082 c row,
    constraint_1083 c row,
    constraint_1084 c row,
    constraint_1085 c row,
    constraint_1086 c row,
    constraint_1087 c row,
    constraint_1088 c row,
    constraint_1089 c row,
    constraint_1090 c row,
    constraint_1091 c row,
    constraint_1092 c row,
    constraint_1093 c row,
    constraint_1094 c row,
    constraint_1095 c row,
    constraint_1096 c row,
    constraint_1097 c row,
    constraint_1098 c row,
    constraint_1099 c row,
    constraint_1100 c row,
    constraint_1101 c row,
    constraint_1102 c row,
    constraint_1103 c row,
    constraint_1104 c row,
    constraint_1105 c row,
    constraint_1106 c row,
    constraint_1107 c row,
    constraint_1108 c row,
    constraint_1109 c row,
    constraint_1110 c row,
    constraint_1111 c row,
    constraint_1112 c row,
    constraint_1113 c row,
    constraint_1114 c row,
    constraint_1115 c row,
    constraint_1116 c row,
    constraint_1117 c row,
    constraint_1118 c row,
    constraint_1119 c row,
    constraint_1120 c row,
    constraint_1121 c row,
    constraint_1122 c row,
    constraint_1123 c row,
    constraint_1124 c row,
    constraint_1125 c row,
    constraint_1126 c row,
    constraint_1127 c row,
    constraint_1128 c row,
    constraint_1129 c row,
    constraint_1130 c row,
    constraint_1131 c row,
    constraint_1132 c row,
    constraint_1133 c row,
    constraint_1134 c row,
    constraint_1135 c row,
    constraint_1136 c row,
    constraint_1137 c row,
    constraint_1138 c row,
    constraint_1139 c row,
    constraint_1140 c row,
    constraint_1141 c row,
    constraint_1142 c row,
    constraint_1143 c row,
    constraint_1144 c row,
    constraint_1145 c row,
    constraint_1146 c row,
    constraint_1147 c row,
    constraint_1148 c row,
    constraint_1149 c row,
    constraint_1150 c row,
    constraint_1151 c row,
    constraint_1152 c row,
    constraint_1153 c row,
    constraint_1154 c row,
    constraint_1155 c row,
    constraint_1156 c row,
    constraint_1157 c row,
    constraint_1158 c row,
    constraint_1159 c row,
    constraint_1160 c row,
    constraint_1161 c row,
    constraint_1162 c row,
    constraint_1163 c row,
    constraint_1164 c row,
    constraint_1165 c row,
    constraint_1166 c row,
    constraint_1167 c row,
    constraint_1168 c row,
    constraint_1169 c row,
    constraint_1170 c row,
    constraint_1171 c row,
    constraint_1172 c row,
    constraint_1173 c row,
    constraint_1174 c row,
    constraint_1175 c row,
    constraint_1176 c row,
    constraint_1177 c row,
    constraint_1178 c row,
    constraint_1179 c row,
    constraint_1180 c row,
    constraint_1181 c row,
    constraint_1182 c row,
    constraint_1183 c row,
    constraint_1184 c row,
    constraint_1185 c row,
    constraint_1186 c row,
    constraint_1187 c row,
    constraint_1188 c row,
    constraint_1189 c row,
    constraint_1190 c row,
    constraint_1191 c row,
    constraint_1192 c row,
    constraint_1193 c row,
    constraint_1194 c row,
    constraint_1195 c row,
    constraint_1196 c row,
    constraint_1197 c row,
    constraint_1198 c row,
    constraint_1199 c row,
    constraint_1200 c row,
    constraint_1201 c row,
    constraint_1202 c row,
    constraint_1203 c row,
    constraint_1204 c row,
    constraint_1205 c row,
    constraint_1206 c row,
    constraint_1207 c row,
    constraint_1208 c row,
    constraint_1209 c row,
    constraint_1210 c row,
    constraint_1211 c row,
    constraint_1212 c row,
    constraint_1213 c row,
    constraint_1214 c row,
    constraint_1215 c row,
    constraint_1216 c row,
    constraint_1217 c row,
    constraint_1218 c row,
    constraint_1219 c row,
    constraint_1220 c row,
    constraint_1221 c row,
    constraint_1222 c row,
    constraint_1223 c row,
    constraint_1224 c row,
    constraint_1225 c row,
    constraint_1226 c row,
    constraint_1227 c row,
    constraint_1228 c row,
    constraint_1229 c row
  ]

-- APrime group 1 (340 items)
def seg_E_ap_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1230 c row,
    constraint_1231 c row,
    constraint_1232 c row,
    constraint_1233 c row,
    constraint_1234 c row,
    constraint_1235 c row,
    constraint_1236 c row,
    constraint_1237 c row,
    constraint_1238 c row,
    constraint_1239 c row,
    constraint_1240 c row,
    constraint_1241 c row,
    constraint_1242 c row,
    constraint_1243 c row,
    constraint_1244 c row,
    constraint_1245 c row,
    constraint_1246 c row,
    constraint_1247 c row,
    constraint_1248 c row,
    constraint_1249 c row,
    constraint_1250 c row,
    constraint_1251 c row,
    constraint_1252 c row,
    constraint_1253 c row,
    constraint_1254 c row,
    constraint_1255 c row,
    constraint_1256 c row,
    constraint_1257 c row,
    constraint_1258 c row,
    constraint_1259 c row,
    constraint_1260 c row,
    constraint_1261 c row,
    constraint_1262 c row,
    constraint_1263 c row,
    constraint_1264 c row,
    constraint_1265 c row,
    constraint_1266 c row,
    constraint_1267 c row,
    constraint_1268 c row,
    constraint_1269 c row,
    constraint_1270 c row,
    constraint_1271 c row,
    constraint_1272 c row,
    constraint_1273 c row,
    constraint_1274 c row,
    constraint_1275 c row,
    constraint_1276 c row,
    constraint_1277 c row,
    constraint_1278 c row,
    constraint_1279 c row,
    constraint_1280 c row,
    constraint_1281 c row,
    constraint_1282 c row,
    constraint_1283 c row,
    constraint_1284 c row,
    constraint_1285 c row,
    constraint_1286 c row,
    constraint_1287 c row,
    constraint_1288 c row,
    constraint_1289 c row,
    constraint_1290 c row,
    constraint_1291 c row,
    constraint_1292 c row,
    constraint_1293 c row,
    constraint_1294 c row,
    constraint_1295 c row,
    constraint_1296 c row,
    constraint_1297 c row,
    constraint_1298 c row,
    constraint_1299 c row,
    constraint_1300 c row,
    constraint_1301 c row,
    constraint_1302 c row,
    constraint_1303 c row,
    constraint_1304 c row,
    constraint_1305 c row,
    constraint_1306 c row,
    constraint_1307 c row,
    constraint_1308 c row,
    constraint_1309 c row,
    constraint_1310 c row,
    constraint_1311 c row,
    constraint_1312 c row,
    constraint_1313 c row,
    constraint_1314 c row,
    constraint_1315 c row,
    constraint_1316 c row,
    constraint_1317 c row,
    constraint_1318 c row,
    constraint_1319 c row,
    constraint_1320 c row,
    constraint_1321 c row,
    constraint_1322 c row,
    constraint_1323 c row,
    constraint_1324 c row,
    constraint_1325 c row,
    constraint_1326 c row,
    constraint_1327 c row,
    constraint_1328 c row,
    constraint_1329 c row,
    constraint_1330 c row,
    constraint_1331 c row,
    constraint_1332 c row,
    constraint_1333 c row,
    constraint_1334 c row,
    constraint_1335 c row,
    constraint_1336 c row,
    constraint_1337 c row,
    constraint_1338 c row,
    constraint_1339 c row,
    constraint_1340 c row,
    constraint_1341 c row,
    constraint_1342 c row,
    constraint_1343 c row,
    constraint_1344 c row,
    constraint_1345 c row,
    constraint_1346 c row,
    constraint_1347 c row,
    constraint_1348 c row,
    constraint_1349 c row,
    constraint_1350 c row,
    constraint_1351 c row,
    constraint_1352 c row,
    constraint_1353 c row,
    constraint_1354 c row,
    constraint_1355 c row,
    constraint_1356 c row,
    constraint_1357 c row,
    constraint_1358 c row,
    constraint_1359 c row,
    constraint_1360 c row,
    constraint_1361 c row,
    constraint_1362 c row,
    constraint_1363 c row,
    constraint_1364 c row,
    constraint_1365 c row,
    constraint_1366 c row,
    constraint_1367 c row,
    constraint_1368 c row,
    constraint_1369 c row,
    constraint_1370 c row,
    constraint_1371 c row,
    constraint_1372 c row,
    constraint_1373 c row,
    constraint_1374 c row,
    constraint_1375 c row,
    constraint_1376 c row,
    constraint_1377 c row,
    constraint_1378 c row,
    constraint_1379 c row,
    constraint_1380 c row,
    constraint_1381 c row,
    constraint_1382 c row,
    constraint_1383 c row,
    constraint_1384 c row,
    constraint_1385 c row,
    constraint_1386 c row,
    constraint_1387 c row,
    constraint_1388 c row,
    constraint_1389 c row,
    constraint_1390 c row,
    constraint_1391 c row,
    constraint_1392 c row,
    constraint_1393 c row,
    constraint_1394 c row,
    constraint_1395 c row,
    constraint_1396 c row,
    constraint_1397 c row,
    constraint_1398 c row,
    constraint_1399 c row,
    constraint_1400 c row,
    constraint_1401 c row,
    constraint_1402 c row,
    constraint_1403 c row,
    constraint_1404 c row,
    constraint_1405 c row,
    constraint_1406 c row,
    constraint_1407 c row,
    constraint_1408 c row,
    constraint_1409 c row,
    constraint_1410 c row,
    constraint_1411 c row,
    constraint_1412 c row,
    constraint_1413 c row,
    constraint_1414 c row,
    constraint_1415 c row,
    constraint_1416 c row,
    constraint_1417 c row,
    constraint_1418 c row,
    constraint_1419 c row,
    constraint_1420 c row,
    constraint_1421 c row,
    constraint_1422 c row,
    constraint_1423 c row,
    constraint_1424 c row,
    constraint_1425 c row,
    constraint_1426 c row,
    constraint_1427 c row,
    constraint_1428 c row,
    constraint_1429 c row,
    constraint_1430 c row,
    constraint_1431 c row,
    constraint_1432 c row,
    constraint_1433 c row,
    constraint_1434 c row,
    constraint_1435 c row,
    constraint_1436 c row,
    constraint_1437 c row,
    constraint_1438 c row,
    constraint_1439 c row,
    constraint_1440 c row,
    constraint_1441 c row,
    constraint_1442 c row,
    constraint_1443 c row,
    constraint_1444 c row,
    constraint_1445 c row,
    constraint_1446 c row,
    constraint_1447 c row,
    constraint_1448 c row,
    constraint_1449 c row,
    constraint_1450 c row,
    constraint_1451 c row,
    constraint_1452 c row,
    constraint_1453 c row,
    constraint_1454 c row,
    constraint_1455 c row,
    constraint_1456 c row,
    constraint_1457 c row,
    constraint_1458 c row,
    constraint_1459 c row,
    constraint_1460 c row,
    constraint_1461 c row,
    constraint_1462 c row,
    constraint_1463 c row,
    constraint_1464 c row,
    constraint_1465 c row,
    constraint_1466 c row,
    constraint_1467 c row,
    constraint_1468 c row,
    constraint_1469 c row,
    constraint_1470 c row,
    constraint_1471 c row,
    constraint_1472 c row,
    constraint_1473 c row,
    constraint_1474 c row,
    constraint_1475 c row,
    constraint_1476 c row,
    constraint_1477 c row,
    constraint_1478 c row,
    constraint_1479 c row,
    constraint_1480 c row,
    constraint_1481 c row,
    constraint_1482 c row,
    constraint_1483 c row,
    constraint_1484 c row,
    constraint_1485 c row,
    constraint_1486 c row,
    constraint_1487 c row,
    constraint_1488 c row,
    constraint_1489 c row,
    constraint_1490 c row,
    constraint_1491 c row,
    constraint_1492 c row,
    constraint_1493 c row,
    constraint_1494 c row,
    constraint_1495 c row,
    constraint_1496 c row,
    constraint_1497 c row,
    constraint_1498 c row,
    constraint_1499 c row,
    constraint_1500 c row,
    constraint_1501 c row,
    constraint_1502 c row,
    constraint_1503 c row,
    constraint_1504 c row,
    constraint_1505 c row,
    constraint_1506 c row,
    constraint_1507 c row,
    constraint_1508 c row,
    constraint_1509 c row,
    constraint_1510 c row,
    constraint_1511 c row,
    constraint_1512 c row,
    constraint_1513 c row,
    constraint_1514 c row,
    constraint_1515 c row,
    constraint_1516 c row,
    constraint_1517 c row,
    constraint_1518 c row,
    constraint_1519 c row,
    constraint_1520 c row,
    constraint_1521 c row,
    constraint_1522 c row,
    constraint_1523 c row,
    constraint_1524 c row,
    constraint_1525 c row,
    constraint_1526 c row,
    constraint_1527 c row,
    constraint_1528 c row,
    constraint_1529 c row,
    constraint_1530 c row,
    constraint_1531 c row,
    constraint_1532 c row,
    constraint_1533 c row,
    constraint_1534 c row,
    constraint_1535 c row,
    constraint_1536 c row,
    constraint_1537 c row,
    constraint_1538 c row,
    constraint_1539 c row,
    constraint_1540 c row,
    constraint_1541 c row,
    constraint_1542 c row,
    constraint_1543 c row,
    constraint_1544 c row,
    constraint_1545 c row,
    constraint_1546 c row,
    constraint_1547 c row,
    constraint_1548 c row,
    constraint_1549 c row,
    constraint_1550 c row,
    constraint_1551 c row,
    constraint_1552 c row,
    constraint_1553 c row,
    constraint_1554 c row,
    constraint_1555 c row,
    constraint_1556 c row,
    constraint_1557 c row,
    constraint_1558 c row,
    constraint_1559 c row,
    constraint_1560 c row,
    constraint_1561 c row,
    constraint_1562 c row,
    constraint_1563 c row,
    constraint_1564 c row,
    constraint_1565 c row,
    constraint_1566 c row,
    constraint_1567 c row,
    constraint_1568 c row,
    constraint_1569 c row
  ]

-- APrime group 2 (340 items)
def seg_E_ap_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1570 c row,
    constraint_1571 c row,
    constraint_1572 c row,
    constraint_1573 c row,
    constraint_1574 c row,
    constraint_1575 c row,
    constraint_1576 c row,
    constraint_1577 c row,
    constraint_1578 c row,
    constraint_1579 c row,
    constraint_1580 c row,
    constraint_1581 c row,
    constraint_1582 c row,
    constraint_1583 c row,
    constraint_1584 c row,
    constraint_1585 c row,
    constraint_1586 c row,
    constraint_1587 c row,
    constraint_1588 c row,
    constraint_1589 c row,
    constraint_1590 c row,
    constraint_1591 c row,
    constraint_1592 c row,
    constraint_1593 c row,
    constraint_1594 c row,
    constraint_1595 c row,
    constraint_1596 c row,
    constraint_1597 c row,
    constraint_1598 c row,
    constraint_1599 c row,
    constraint_1600 c row,
    constraint_1601 c row,
    constraint_1602 c row,
    constraint_1603 c row,
    constraint_1604 c row,
    constraint_1605 c row,
    constraint_1606 c row,
    constraint_1607 c row,
    constraint_1608 c row,
    constraint_1609 c row,
    constraint_1610 c row,
    constraint_1611 c row,
    constraint_1612 c row,
    constraint_1613 c row,
    constraint_1614 c row,
    constraint_1615 c row,
    constraint_1616 c row,
    constraint_1617 c row,
    constraint_1618 c row,
    constraint_1619 c row,
    constraint_1620 c row,
    constraint_1621 c row,
    constraint_1622 c row,
    constraint_1623 c row,
    constraint_1624 c row,
    constraint_1625 c row,
    constraint_1626 c row,
    constraint_1627 c row,
    constraint_1628 c row,
    constraint_1629 c row,
    constraint_1630 c row,
    constraint_1631 c row,
    constraint_1632 c row,
    constraint_1633 c row,
    constraint_1634 c row,
    constraint_1635 c row,
    constraint_1636 c row,
    constraint_1637 c row,
    constraint_1638 c row,
    constraint_1639 c row,
    constraint_1640 c row,
    constraint_1641 c row,
    constraint_1642 c row,
    constraint_1643 c row,
    constraint_1644 c row,
    constraint_1645 c row,
    constraint_1646 c row,
    constraint_1647 c row,
    constraint_1648 c row,
    constraint_1649 c row,
    constraint_1650 c row,
    constraint_1651 c row,
    constraint_1652 c row,
    constraint_1653 c row,
    constraint_1654 c row,
    constraint_1655 c row,
    constraint_1656 c row,
    constraint_1657 c row,
    constraint_1658 c row,
    constraint_1659 c row,
    constraint_1660 c row,
    constraint_1661 c row,
    constraint_1662 c row,
    constraint_1663 c row,
    constraint_1664 c row,
    constraint_1665 c row,
    constraint_1666 c row,
    constraint_1667 c row,
    constraint_1668 c row,
    constraint_1669 c row,
    constraint_1670 c row,
    constraint_1671 c row,
    constraint_1672 c row,
    constraint_1673 c row,
    constraint_1674 c row,
    constraint_1675 c row,
    constraint_1676 c row,
    constraint_1677 c row,
    constraint_1678 c row,
    constraint_1679 c row,
    constraint_1680 c row,
    constraint_1681 c row,
    constraint_1682 c row,
    constraint_1683 c row,
    constraint_1684 c row,
    constraint_1685 c row,
    constraint_1686 c row,
    constraint_1687 c row,
    constraint_1688 c row,
    constraint_1689 c row,
    constraint_1690 c row,
    constraint_1691 c row,
    constraint_1692 c row,
    constraint_1693 c row,
    constraint_1694 c row,
    constraint_1695 c row,
    constraint_1696 c row,
    constraint_1697 c row,
    constraint_1698 c row,
    constraint_1699 c row,
    constraint_1700 c row,
    constraint_1701 c row,
    constraint_1702 c row,
    constraint_1703 c row,
    constraint_1704 c row,
    constraint_1705 c row,
    constraint_1706 c row,
    constraint_1707 c row,
    constraint_1708 c row,
    constraint_1709 c row,
    constraint_1710 c row,
    constraint_1711 c row,
    constraint_1712 c row,
    constraint_1713 c row,
    constraint_1714 c row,
    constraint_1715 c row,
    constraint_1716 c row,
    constraint_1717 c row,
    constraint_1718 c row,
    constraint_1719 c row,
    constraint_1720 c row,
    constraint_1721 c row,
    constraint_1722 c row,
    constraint_1723 c row,
    constraint_1724 c row,
    constraint_1725 c row,
    constraint_1726 c row,
    constraint_1727 c row,
    constraint_1728 c row,
    constraint_1729 c row,
    constraint_1730 c row,
    constraint_1731 c row,
    constraint_1732 c row,
    constraint_1733 c row,
    constraint_1734 c row,
    constraint_1735 c row,
    constraint_1736 c row,
    constraint_1737 c row,
    constraint_1738 c row,
    constraint_1739 c row,
    constraint_1740 c row,
    constraint_1741 c row,
    constraint_1742 c row,
    constraint_1743 c row,
    constraint_1744 c row,
    constraint_1745 c row,
    constraint_1746 c row,
    constraint_1747 c row,
    constraint_1748 c row,
    constraint_1749 c row,
    constraint_1750 c row,
    constraint_1751 c row,
    constraint_1752 c row,
    constraint_1753 c row,
    constraint_1754 c row,
    constraint_1755 c row,
    constraint_1756 c row,
    constraint_1757 c row,
    constraint_1758 c row,
    constraint_1759 c row,
    constraint_1760 c row,
    constraint_1761 c row,
    constraint_1762 c row,
    constraint_1763 c row,
    constraint_1764 c row,
    constraint_1765 c row,
    constraint_1766 c row,
    constraint_1767 c row,
    constraint_1768 c row,
    constraint_1769 c row,
    constraint_1770 c row,
    constraint_1771 c row,
    constraint_1772 c row,
    constraint_1773 c row,
    constraint_1774 c row,
    constraint_1775 c row,
    constraint_1776 c row,
    constraint_1777 c row,
    constraint_1778 c row,
    constraint_1779 c row,
    constraint_1780 c row,
    constraint_1781 c row,
    constraint_1782 c row,
    constraint_1783 c row,
    constraint_1784 c row,
    constraint_1785 c row,
    constraint_1786 c row,
    constraint_1787 c row,
    constraint_1788 c row,
    constraint_1789 c row,
    constraint_1790 c row,
    constraint_1791 c row,
    constraint_1792 c row,
    constraint_1793 c row,
    constraint_1794 c row,
    constraint_1795 c row,
    constraint_1796 c row,
    constraint_1797 c row,
    constraint_1798 c row,
    constraint_1799 c row,
    constraint_1800 c row,
    constraint_1801 c row,
    constraint_1802 c row,
    constraint_1803 c row,
    constraint_1804 c row,
    constraint_1805 c row,
    constraint_1806 c row,
    constraint_1807 c row,
    constraint_1808 c row,
    constraint_1809 c row,
    constraint_1810 c row,
    constraint_1811 c row,
    constraint_1812 c row,
    constraint_1813 c row,
    constraint_1814 c row,
    constraint_1815 c row,
    constraint_1816 c row,
    constraint_1817 c row,
    constraint_1818 c row,
    constraint_1819 c row,
    constraint_1820 c row,
    constraint_1821 c row,
    constraint_1822 c row,
    constraint_1823 c row,
    constraint_1824 c row,
    constraint_1825 c row,
    constraint_1826 c row,
    constraint_1827 c row,
    constraint_1828 c row,
    constraint_1829 c row,
    constraint_1830 c row,
    constraint_1831 c row,
    constraint_1832 c row,
    constraint_1833 c row,
    constraint_1834 c row,
    constraint_1835 c row,
    constraint_1836 c row,
    constraint_1837 c row,
    constraint_1838 c row,
    constraint_1839 c row,
    constraint_1840 c row,
    constraint_1841 c row,
    constraint_1842 c row,
    constraint_1843 c row,
    constraint_1844 c row,
    constraint_1845 c row,
    constraint_1846 c row,
    constraint_1847 c row,
    constraint_1848 c row,
    constraint_1849 c row,
    constraint_1850 c row,
    constraint_1851 c row,
    constraint_1852 c row,
    constraint_1853 c row,
    constraint_1854 c row,
    constraint_1855 c row,
    constraint_1856 c row,
    constraint_1857 c row,
    constraint_1858 c row,
    constraint_1859 c row,
    constraint_1860 c row,
    constraint_1861 c row,
    constraint_1862 c row,
    constraint_1863 c row,
    constraint_1864 c row,
    constraint_1865 c row,
    constraint_1866 c row,
    constraint_1867 c row,
    constraint_1868 c row,
    constraint_1869 c row,
    constraint_1870 c row,
    constraint_1871 c row,
    constraint_1872 c row,
    constraint_1873 c row,
    constraint_1874 c row,
    constraint_1875 c row,
    constraint_1876 c row,
    constraint_1877 c row,
    constraint_1878 c row,
    constraint_1879 c row,
    constraint_1880 c row,
    constraint_1881 c row,
    constraint_1882 c row,
    constraint_1883 c row,
    constraint_1884 c row,
    constraint_1885 c row,
    constraint_1886 c row,
    constraint_1887 c row,
    constraint_1888 c row,
    constraint_1889 c row,
    constraint_1890 c row,
    constraint_1891 c row,
    constraint_1892 c row,
    constraint_1893 c row,
    constraint_1894 c row,
    constraint_1895 c row,
    constraint_1896 c row,
    constraint_1897 c row,
    constraint_1898 c row,
    constraint_1899 c row,
    constraint_1900 c row,
    constraint_1901 c row,
    constraint_1902 c row,
    constraint_1903 c row,
    constraint_1904 c row,
    constraint_1905 c row,
    constraint_1906 c row,
    constraint_1907 c row,
    constraint_1908 c row,
    constraint_1909 c row
  ]

-- APrime group 3 (340 items)
def seg_E_ap_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1910 c row,
    constraint_1911 c row,
    constraint_1912 c row,
    constraint_1913 c row,
    constraint_1914 c row,
    constraint_1915 c row,
    constraint_1916 c row,
    constraint_1917 c row,
    constraint_1918 c row,
    constraint_1919 c row,
    constraint_1920 c row,
    constraint_1921 c row,
    constraint_1922 c row,
    constraint_1923 c row,
    constraint_1924 c row,
    constraint_1925 c row,
    constraint_1926 c row,
    constraint_1927 c row,
    constraint_1928 c row,
    constraint_1929 c row,
    constraint_1930 c row,
    constraint_1931 c row,
    constraint_1932 c row,
    constraint_1933 c row,
    constraint_1934 c row,
    constraint_1935 c row,
    constraint_1936 c row,
    constraint_1937 c row,
    constraint_1938 c row,
    constraint_1939 c row,
    constraint_1940 c row,
    constraint_1941 c row,
    constraint_1942 c row,
    constraint_1943 c row,
    constraint_1944 c row,
    constraint_1945 c row,
    constraint_1946 c row,
    constraint_1947 c row,
    constraint_1948 c row,
    constraint_1949 c row,
    constraint_1950 c row,
    constraint_1951 c row,
    constraint_1952 c row,
    constraint_1953 c row,
    constraint_1954 c row,
    constraint_1955 c row,
    constraint_1956 c row,
    constraint_1957 c row,
    constraint_1958 c row,
    constraint_1959 c row,
    constraint_1960 c row,
    constraint_1961 c row,
    constraint_1962 c row,
    constraint_1963 c row,
    constraint_1964 c row,
    constraint_1965 c row,
    constraint_1966 c row,
    constraint_1967 c row,
    constraint_1968 c row,
    constraint_1969 c row,
    constraint_1970 c row,
    constraint_1971 c row,
    constraint_1972 c row,
    constraint_1973 c row,
    constraint_1974 c row,
    constraint_1975 c row,
    constraint_1976 c row,
    constraint_1977 c row,
    constraint_1978 c row,
    constraint_1979 c row,
    constraint_1980 c row,
    constraint_1981 c row,
    constraint_1982 c row,
    constraint_1983 c row,
    constraint_1984 c row,
    constraint_1985 c row,
    constraint_1986 c row,
    constraint_1987 c row,
    constraint_1988 c row,
    constraint_1989 c row,
    constraint_1990 c row,
    constraint_1991 c row,
    constraint_1992 c row,
    constraint_1993 c row,
    constraint_1994 c row,
    constraint_1995 c row,
    constraint_1996 c row,
    constraint_1997 c row,
    constraint_1998 c row,
    constraint_1999 c row,
    constraint_2000 c row,
    constraint_2001 c row,
    constraint_2002 c row,
    constraint_2003 c row,
    constraint_2004 c row,
    constraint_2005 c row,
    constraint_2006 c row,
    constraint_2007 c row,
    constraint_2008 c row,
    constraint_2009 c row,
    constraint_2010 c row,
    constraint_2011 c row,
    constraint_2012 c row,
    constraint_2013 c row,
    constraint_2014 c row,
    constraint_2015 c row,
    constraint_2016 c row,
    constraint_2017 c row,
    constraint_2018 c row,
    constraint_2019 c row,
    constraint_2020 c row,
    constraint_2021 c row,
    constraint_2022 c row,
    constraint_2023 c row,
    constraint_2024 c row,
    constraint_2025 c row,
    constraint_2026 c row,
    constraint_2027 c row,
    constraint_2028 c row,
    constraint_2029 c row,
    constraint_2030 c row,
    constraint_2031 c row,
    constraint_2032 c row,
    constraint_2033 c row,
    constraint_2034 c row,
    constraint_2035 c row,
    constraint_2036 c row,
    constraint_2037 c row,
    constraint_2038 c row,
    constraint_2039 c row,
    constraint_2040 c row,
    constraint_2041 c row,
    constraint_2042 c row,
    constraint_2043 c row,
    constraint_2044 c row,
    constraint_2045 c row,
    constraint_2046 c row,
    constraint_2047 c row,
    constraint_2048 c row,
    constraint_2049 c row,
    constraint_2050 c row,
    constraint_2051 c row,
    constraint_2052 c row,
    constraint_2053 c row,
    constraint_2054 c row,
    constraint_2055 c row,
    constraint_2056 c row,
    constraint_2057 c row,
    constraint_2058 c row,
    constraint_2059 c row,
    constraint_2060 c row,
    constraint_2061 c row,
    constraint_2062 c row,
    constraint_2063 c row,
    constraint_2064 c row,
    constraint_2065 c row,
    constraint_2066 c row,
    constraint_2067 c row,
    constraint_2068 c row,
    constraint_2069 c row,
    constraint_2070 c row,
    constraint_2071 c row,
    constraint_2072 c row,
    constraint_2073 c row,
    constraint_2074 c row,
    constraint_2075 c row,
    constraint_2076 c row,
    constraint_2077 c row,
    constraint_2078 c row,
    constraint_2079 c row,
    constraint_2080 c row,
    constraint_2081 c row,
    constraint_2082 c row,
    constraint_2083 c row,
    constraint_2084 c row,
    constraint_2085 c row,
    constraint_2086 c row,
    constraint_2087 c row,
    constraint_2088 c row,
    constraint_2089 c row,
    constraint_2090 c row,
    constraint_2091 c row,
    constraint_2092 c row,
    constraint_2093 c row,
    constraint_2094 c row,
    constraint_2095 c row,
    constraint_2096 c row,
    constraint_2097 c row,
    constraint_2098 c row,
    constraint_2099 c row,
    constraint_2100 c row,
    constraint_2101 c row,
    constraint_2102 c row,
    constraint_2103 c row,
    constraint_2104 c row,
    constraint_2105 c row,
    constraint_2106 c row,
    constraint_2107 c row,
    constraint_2108 c row,
    constraint_2109 c row,
    constraint_2110 c row,
    constraint_2111 c row,
    constraint_2112 c row,
    constraint_2113 c row,
    constraint_2114 c row,
    constraint_2115 c row,
    constraint_2116 c row,
    constraint_2117 c row,
    constraint_2118 c row,
    constraint_2119 c row,
    constraint_2120 c row,
    constraint_2121 c row,
    constraint_2122 c row,
    constraint_2123 c row,
    constraint_2124 c row,
    constraint_2125 c row,
    constraint_2126 c row,
    constraint_2127 c row,
    constraint_2128 c row,
    constraint_2129 c row,
    constraint_2130 c row,
    constraint_2131 c row,
    constraint_2132 c row,
    constraint_2133 c row,
    constraint_2134 c row,
    constraint_2135 c row,
    constraint_2136 c row,
    constraint_2137 c row,
    constraint_2138 c row,
    constraint_2139 c row,
    constraint_2140 c row,
    constraint_2141 c row,
    constraint_2142 c row,
    constraint_2143 c row,
    constraint_2144 c row,
    constraint_2145 c row,
    constraint_2146 c row,
    constraint_2147 c row,
    constraint_2148 c row,
    constraint_2149 c row,
    constraint_2150 c row,
    constraint_2151 c row,
    constraint_2152 c row,
    constraint_2153 c row,
    constraint_2154 c row,
    constraint_2155 c row,
    constraint_2156 c row,
    constraint_2157 c row,
    constraint_2158 c row,
    constraint_2159 c row,
    constraint_2160 c row,
    constraint_2161 c row,
    constraint_2162 c row,
    constraint_2163 c row,
    constraint_2164 c row,
    constraint_2165 c row,
    constraint_2166 c row,
    constraint_2167 c row,
    constraint_2168 c row,
    constraint_2169 c row,
    constraint_2170 c row,
    constraint_2171 c row,
    constraint_2172 c row,
    constraint_2173 c row,
    constraint_2174 c row,
    constraint_2175 c row,
    constraint_2176 c row,
    constraint_2177 c row,
    constraint_2178 c row,
    constraint_2179 c row,
    constraint_2180 c row,
    constraint_2181 c row,
    constraint_2182 c row,
    constraint_2183 c row,
    constraint_2184 c row,
    constraint_2185 c row,
    constraint_2186 c row,
    constraint_2187 c row,
    constraint_2188 c row,
    constraint_2189 c row,
    constraint_2190 c row,
    constraint_2191 c row,
    constraint_2192 c row,
    constraint_2193 c row,
    constraint_2194 c row,
    constraint_2195 c row,
    constraint_2196 c row,
    constraint_2197 c row,
    constraint_2198 c row,
    constraint_2199 c row,
    constraint_2200 c row,
    constraint_2201 c row,
    constraint_2202 c row,
    constraint_2203 c row,
    constraint_2204 c row,
    constraint_2205 c row,
    constraint_2206 c row,
    constraint_2207 c row,
    constraint_2208 c row,
    constraint_2209 c row,
    constraint_2210 c row,
    constraint_2211 c row,
    constraint_2212 c row,
    constraint_2213 c row,
    constraint_2214 c row,
    constraint_2215 c row,
    constraint_2216 c row,
    constraint_2217 c row,
    constraint_2218 c row,
    constraint_2219 c row,
    constraint_2220 c row,
    constraint_2221 c row,
    constraint_2222 c row,
    constraint_2223 c row,
    constraint_2224 c row,
    constraint_2225 c row,
    constraint_2226 c row,
    constraint_2227 c row,
    constraint_2228 c row,
    constraint_2229 c row,
    constraint_2230 c row,
    constraint_2231 c row,
    constraint_2232 c row,
    constraint_2233 c row,
    constraint_2234 c row,
    constraint_2235 c row,
    constraint_2236 c row,
    constraint_2237 c row,
    constraint_2238 c row,
    constraint_2239 c row,
    constraint_2240 c row,
    constraint_2241 c row,
    constraint_2242 c row,
    constraint_2243 c row,
    constraint_2244 c row,
    constraint_2245 c row,
    constraint_2246 c row,
    constraint_2247 c row,
    constraint_2248 c row,
    constraint_2249 c row
  ]

-- APrime group 4 (340 items)
def seg_E_ap_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2250 c row,
    constraint_2251 c row,
    constraint_2252 c row,
    constraint_2253 c row,
    constraint_2254 c row,
    constraint_2255 c row,
    constraint_2256 c row,
    constraint_2257 c row,
    constraint_2258 c row,
    constraint_2259 c row,
    constraint_2260 c row,
    constraint_2261 c row,
    constraint_2262 c row,
    constraint_2263 c row,
    constraint_2264 c row,
    constraint_2265 c row,
    constraint_2266 c row,
    constraint_2267 c row,
    constraint_2268 c row,
    constraint_2269 c row,
    constraint_2270 c row,
    constraint_2271 c row,
    constraint_2272 c row,
    constraint_2273 c row,
    constraint_2274 c row,
    constraint_2275 c row,
    constraint_2276 c row,
    constraint_2277 c row,
    constraint_2278 c row,
    constraint_2279 c row,
    constraint_2280 c row,
    constraint_2281 c row,
    constraint_2282 c row,
    constraint_2283 c row,
    constraint_2284 c row,
    constraint_2285 c row,
    constraint_2286 c row,
    constraint_2287 c row,
    constraint_2288 c row,
    constraint_2289 c row,
    constraint_2290 c row,
    constraint_2291 c row,
    constraint_2292 c row,
    constraint_2293 c row,
    constraint_2294 c row,
    constraint_2295 c row,
    constraint_2296 c row,
    constraint_2297 c row,
    constraint_2298 c row,
    constraint_2299 c row,
    constraint_2300 c row,
    constraint_2301 c row,
    constraint_2302 c row,
    constraint_2303 c row,
    constraint_2304 c row,
    constraint_2305 c row,
    constraint_2306 c row,
    constraint_2307 c row,
    constraint_2308 c row,
    constraint_2309 c row,
    constraint_2310 c row,
    constraint_2311 c row,
    constraint_2312 c row,
    constraint_2313 c row,
    constraint_2314 c row,
    constraint_2315 c row,
    constraint_2316 c row,
    constraint_2317 c row,
    constraint_2318 c row,
    constraint_2319 c row,
    constraint_2320 c row,
    constraint_2321 c row,
    constraint_2322 c row,
    constraint_2323 c row,
    constraint_2324 c row,
    constraint_2325 c row,
    constraint_2326 c row,
    constraint_2327 c row,
    constraint_2328 c row,
    constraint_2329 c row,
    constraint_2330 c row,
    constraint_2331 c row,
    constraint_2332 c row,
    constraint_2333 c row,
    constraint_2334 c row,
    constraint_2335 c row,
    constraint_2336 c row,
    constraint_2337 c row,
    constraint_2338 c row,
    constraint_2339 c row,
    constraint_2340 c row,
    constraint_2341 c row,
    constraint_2342 c row,
    constraint_2343 c row,
    constraint_2344 c row,
    constraint_2345 c row,
    constraint_2346 c row,
    constraint_2347 c row,
    constraint_2348 c row,
    constraint_2349 c row,
    constraint_2350 c row,
    constraint_2351 c row,
    constraint_2352 c row,
    constraint_2353 c row,
    constraint_2354 c row,
    constraint_2355 c row,
    constraint_2356 c row,
    constraint_2357 c row,
    constraint_2358 c row,
    constraint_2359 c row,
    constraint_2360 c row,
    constraint_2361 c row,
    constraint_2362 c row,
    constraint_2363 c row,
    constraint_2364 c row,
    constraint_2365 c row,
    constraint_2366 c row,
    constraint_2367 c row,
    constraint_2368 c row,
    constraint_2369 c row,
    constraint_2370 c row,
    constraint_2371 c row,
    constraint_2372 c row,
    constraint_2373 c row,
    constraint_2374 c row,
    constraint_2375 c row,
    constraint_2376 c row,
    constraint_2377 c row,
    constraint_2378 c row,
    constraint_2379 c row,
    constraint_2380 c row,
    constraint_2381 c row,
    constraint_2382 c row,
    constraint_2383 c row,
    constraint_2384 c row,
    constraint_2385 c row,
    constraint_2386 c row,
    constraint_2387 c row,
    constraint_2388 c row,
    constraint_2389 c row,
    constraint_2390 c row,
    constraint_2391 c row,
    constraint_2392 c row,
    constraint_2393 c row,
    constraint_2394 c row,
    constraint_2395 c row,
    constraint_2396 c row,
    constraint_2397 c row,
    constraint_2398 c row,
    constraint_2399 c row,
    constraint_2400 c row,
    constraint_2401 c row,
    constraint_2402 c row,
    constraint_2403 c row,
    constraint_2404 c row,
    constraint_2405 c row,
    constraint_2406 c row,
    constraint_2407 c row,
    constraint_2408 c row,
    constraint_2409 c row,
    constraint_2410 c row,
    constraint_2411 c row,
    constraint_2412 c row,
    constraint_2413 c row,
    constraint_2414 c row,
    constraint_2415 c row,
    constraint_2416 c row,
    constraint_2417 c row,
    constraint_2418 c row,
    constraint_2419 c row,
    constraint_2420 c row,
    constraint_2421 c row,
    constraint_2422 c row,
    constraint_2423 c row,
    constraint_2424 c row,
    constraint_2425 c row,
    constraint_2426 c row,
    constraint_2427 c row,
    constraint_2428 c row,
    constraint_2429 c row,
    constraint_2430 c row,
    constraint_2431 c row,
    constraint_2432 c row,
    constraint_2433 c row,
    constraint_2434 c row,
    constraint_2435 c row,
    constraint_2436 c row,
    constraint_2437 c row,
    constraint_2438 c row,
    constraint_2439 c row,
    constraint_2440 c row,
    constraint_2441 c row,
    constraint_2442 c row,
    constraint_2443 c row,
    constraint_2444 c row,
    constraint_2445 c row,
    constraint_2446 c row,
    constraint_2447 c row,
    constraint_2448 c row,
    constraint_2449 c row,
    constraint_2450 c row,
    constraint_2451 c row,
    constraint_2452 c row,
    constraint_2453 c row,
    constraint_2454 c row,
    constraint_2455 c row,
    constraint_2456 c row,
    constraint_2457 c row,
    constraint_2458 c row,
    constraint_2459 c row,
    constraint_2460 c row,
    constraint_2461 c row,
    constraint_2462 c row,
    constraint_2463 c row,
    constraint_2464 c row,
    constraint_2465 c row,
    constraint_2466 c row,
    constraint_2467 c row,
    constraint_2468 c row,
    constraint_2469 c row,
    constraint_2470 c row,
    constraint_2471 c row,
    constraint_2472 c row,
    constraint_2473 c row,
    constraint_2474 c row,
    constraint_2475 c row,
    constraint_2476 c row,
    constraint_2477 c row,
    constraint_2478 c row,
    constraint_2479 c row,
    constraint_2480 c row,
    constraint_2481 c row,
    constraint_2482 c row,
    constraint_2483 c row,
    constraint_2484 c row,
    constraint_2485 c row,
    constraint_2486 c row,
    constraint_2487 c row,
    constraint_2488 c row,
    constraint_2489 c row,
    constraint_2490 c row,
    constraint_2491 c row,
    constraint_2492 c row,
    constraint_2493 c row,
    constraint_2494 c row,
    constraint_2495 c row,
    constraint_2496 c row,
    constraint_2497 c row,
    constraint_2498 c row,
    constraint_2499 c row,
    constraint_2500 c row,
    constraint_2501 c row,
    constraint_2502 c row,
    constraint_2503 c row,
    constraint_2504 c row,
    constraint_2505 c row,
    constraint_2506 c row,
    constraint_2507 c row,
    constraint_2508 c row,
    constraint_2509 c row,
    constraint_2510 c row,
    constraint_2511 c row,
    constraint_2512 c row,
    constraint_2513 c row,
    constraint_2514 c row,
    constraint_2515 c row,
    constraint_2516 c row,
    constraint_2517 c row,
    constraint_2518 c row,
    constraint_2519 c row,
    constraint_2520 c row,
    constraint_2521 c row,
    constraint_2522 c row,
    constraint_2523 c row,
    constraint_2524 c row,
    constraint_2525 c row,
    constraint_2526 c row,
    constraint_2527 c row,
    constraint_2528 c row,
    constraint_2529 c row,
    constraint_2530 c row,
    constraint_2531 c row,
    constraint_2532 c row,
    constraint_2533 c row,
    constraint_2534 c row,
    constraint_2535 c row,
    constraint_2536 c row,
    constraint_2537 c row,
    constraint_2538 c row,
    constraint_2539 c row,
    constraint_2540 c row,
    constraint_2541 c row,
    constraint_2542 c row,
    constraint_2543 c row,
    constraint_2544 c row,
    constraint_2545 c row,
    constraint_2546 c row,
    constraint_2547 c row,
    constraint_2548 c row,
    constraint_2549 c row,
    constraint_2550 c row,
    constraint_2551 c row,
    constraint_2552 c row,
    constraint_2553 c row,
    constraint_2554 c row,
    constraint_2555 c row,
    constraint_2556 c row,
    constraint_2557 c row,
    constraint_2558 c row,
    constraint_2559 c row,
    constraint_2560 c row,
    constraint_2561 c row,
    constraint_2562 c row,
    constraint_2563 c row,
    constraint_2564 c row,
    constraint_2565 c row,
    constraint_2566 c row,
    constraint_2567 c row,
    constraint_2568 c row,
    constraint_2569 c row,
    constraint_2570 c row,
    constraint_2571 c row,
    constraint_2572 c row,
    constraint_2573 c row,
    constraint_2574 c row,
    constraint_2575 c row,
    constraint_2576 c row,
    constraint_2577 c row,
    constraint_2578 c row,
    constraint_2579 c row,
    constraint_2580 c row,
    constraint_2581 c row,
    constraint_2582 c row,
    constraint_2583 c row,
    constraint_2584 c row,
    constraint_2585 c row,
    constraint_2586 c row,
    constraint_2587 c row,
    constraint_2588 c row,
    constraint_2589 c row
  ]

-- Parity (320 items)
def seg_E_parity
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2590 c row,
    constraint_2591 c row,
    constraint_2592 c row,
    constraint_2593 c row,
    constraint_2594 c row,
    constraint_2595 c row,
    constraint_2596 c row,
    constraint_2597 c row,
    constraint_2598 c row,
    constraint_2599 c row,
    constraint_2600 c row,
    constraint_2601 c row,
    constraint_2602 c row,
    constraint_2603 c row,
    constraint_2604 c row,
    constraint_2605 c row,
    constraint_2606 c row,
    constraint_2607 c row,
    constraint_2608 c row,
    constraint_2609 c row,
    constraint_2610 c row,
    constraint_2611 c row,
    constraint_2612 c row,
    constraint_2613 c row,
    constraint_2614 c row,
    constraint_2615 c row,
    constraint_2616 c row,
    constraint_2617 c row,
    constraint_2618 c row,
    constraint_2619 c row,
    constraint_2620 c row,
    constraint_2621 c row,
    constraint_2622 c row,
    constraint_2623 c row,
    constraint_2624 c row,
    constraint_2625 c row,
    constraint_2626 c row,
    constraint_2627 c row,
    constraint_2628 c row,
    constraint_2629 c row,
    constraint_2630 c row,
    constraint_2631 c row,
    constraint_2632 c row,
    constraint_2633 c row,
    constraint_2634 c row,
    constraint_2635 c row,
    constraint_2636 c row,
    constraint_2637 c row,
    constraint_2638 c row,
    constraint_2639 c row,
    constraint_2640 c row,
    constraint_2641 c row,
    constraint_2642 c row,
    constraint_2643 c row,
    constraint_2644 c row,
    constraint_2645 c row,
    constraint_2646 c row,
    constraint_2647 c row,
    constraint_2648 c row,
    constraint_2649 c row,
    constraint_2650 c row,
    constraint_2651 c row,
    constraint_2652 c row,
    constraint_2653 c row,
    constraint_2654 c row,
    constraint_2655 c row,
    constraint_2656 c row,
    constraint_2657 c row,
    constraint_2658 c row,
    constraint_2659 c row,
    constraint_2660 c row,
    constraint_2661 c row,
    constraint_2662 c row,
    constraint_2663 c row,
    constraint_2664 c row,
    constraint_2665 c row,
    constraint_2666 c row,
    constraint_2667 c row,
    constraint_2668 c row,
    constraint_2669 c row,
    constraint_2670 c row,
    constraint_2671 c row,
    constraint_2672 c row,
    constraint_2673 c row,
    constraint_2674 c row,
    constraint_2675 c row,
    constraint_2676 c row,
    constraint_2677 c row,
    constraint_2678 c row,
    constraint_2679 c row,
    constraint_2680 c row,
    constraint_2681 c row,
    constraint_2682 c row,
    constraint_2683 c row,
    constraint_2684 c row,
    constraint_2685 c row,
    constraint_2686 c row,
    constraint_2687 c row,
    constraint_2688 c row,
    constraint_2689 c row,
    constraint_2690 c row,
    constraint_2691 c row,
    constraint_2692 c row,
    constraint_2693 c row,
    constraint_2694 c row,
    constraint_2695 c row,
    constraint_2696 c row,
    constraint_2697 c row,
    constraint_2698 c row,
    constraint_2699 c row,
    constraint_2700 c row,
    constraint_2701 c row,
    constraint_2702 c row,
    constraint_2703 c row,
    constraint_2704 c row,
    constraint_2705 c row,
    constraint_2706 c row,
    constraint_2707 c row,
    constraint_2708 c row,
    constraint_2709 c row,
    constraint_2710 c row,
    constraint_2711 c row,
    constraint_2712 c row,
    constraint_2713 c row,
    constraint_2714 c row,
    constraint_2715 c row,
    constraint_2716 c row,
    constraint_2717 c row,
    constraint_2718 c row,
    constraint_2719 c row,
    constraint_2720 c row,
    constraint_2721 c row,
    constraint_2722 c row,
    constraint_2723 c row,
    constraint_2724 c row,
    constraint_2725 c row,
    constraint_2726 c row,
    constraint_2727 c row,
    constraint_2728 c row,
    constraint_2729 c row,
    constraint_2730 c row,
    constraint_2731 c row,
    constraint_2732 c row,
    constraint_2733 c row,
    constraint_2734 c row,
    constraint_2735 c row,
    constraint_2736 c row,
    constraint_2737 c row,
    constraint_2738 c row,
    constraint_2739 c row,
    constraint_2740 c row,
    constraint_2741 c row,
    constraint_2742 c row,
    constraint_2743 c row,
    constraint_2744 c row,
    constraint_2745 c row,
    constraint_2746 c row,
    constraint_2747 c row,
    constraint_2748 c row,
    constraint_2749 c row,
    constraint_2750 c row,
    constraint_2751 c row,
    constraint_2752 c row,
    constraint_2753 c row,
    constraint_2754 c row,
    constraint_2755 c row,
    constraint_2756 c row,
    constraint_2757 c row,
    constraint_2758 c row,
    constraint_2759 c row,
    constraint_2760 c row,
    constraint_2761 c row,
    constraint_2762 c row,
    constraint_2763 c row,
    constraint_2764 c row,
    constraint_2765 c row,
    constraint_2766 c row,
    constraint_2767 c row,
    constraint_2768 c row,
    constraint_2769 c row,
    constraint_2770 c row,
    constraint_2771 c row,
    constraint_2772 c row,
    constraint_2773 c row,
    constraint_2774 c row,
    constraint_2775 c row,
    constraint_2776 c row,
    constraint_2777 c row,
    constraint_2778 c row,
    constraint_2779 c row,
    constraint_2780 c row,
    constraint_2781 c row,
    constraint_2782 c row,
    constraint_2783 c row,
    constraint_2784 c row,
    constraint_2785 c row,
    constraint_2786 c row,
    constraint_2787 c row,
    constraint_2788 c row,
    constraint_2789 c row,
    constraint_2790 c row,
    constraint_2791 c row,
    constraint_2792 c row,
    constraint_2793 c row,
    constraint_2794 c row,
    constraint_2795 c row,
    constraint_2796 c row,
    constraint_2797 c row,
    constraint_2798 c row,
    constraint_2799 c row,
    constraint_2800 c row,
    constraint_2801 c row,
    constraint_2802 c row,
    constraint_2803 c row,
    constraint_2804 c row,
    constraint_2805 c row,
    constraint_2806 c row,
    constraint_2807 c row,
    constraint_2808 c row,
    constraint_2809 c row,
    constraint_2810 c row,
    constraint_2811 c row,
    constraint_2812 c row,
    constraint_2813 c row,
    constraint_2814 c row,
    constraint_2815 c row,
    constraint_2816 c row,
    constraint_2817 c row,
    constraint_2818 c row,
    constraint_2819 c row,
    constraint_2820 c row,
    constraint_2821 c row,
    constraint_2822 c row,
    constraint_2823 c row,
    constraint_2824 c row,
    constraint_2825 c row,
    constraint_2826 c row,
    constraint_2827 c row,
    constraint_2828 c row,
    constraint_2829 c row,
    constraint_2830 c row,
    constraint_2831 c row,
    constraint_2832 c row,
    constraint_2833 c row,
    constraint_2834 c row,
    constraint_2835 c row,
    constraint_2836 c row,
    constraint_2837 c row,
    constraint_2838 c row,
    constraint_2839 c row,
    constraint_2840 c row,
    constraint_2841 c row,
    constraint_2842 c row,
    constraint_2843 c row,
    constraint_2844 c row,
    constraint_2845 c row,
    constraint_2846 c row,
    constraint_2847 c row,
    constraint_2848 c row,
    constraint_2849 c row,
    constraint_2850 c row,
    constraint_2851 c row,
    constraint_2852 c row,
    constraint_2853 c row,
    constraint_2854 c row,
    constraint_2855 c row,
    constraint_2856 c row,
    constraint_2857 c row,
    constraint_2858 c row,
    constraint_2859 c row,
    constraint_2860 c row,
    constraint_2861 c row,
    constraint_2862 c row,
    constraint_2863 c row,
    constraint_2864 c row,
    constraint_2865 c row,
    constraint_2866 c row,
    constraint_2867 c row,
    constraint_2868 c row,
    constraint_2869 c row,
    constraint_2870 c row,
    constraint_2871 c row,
    constraint_2872 c row,
    constraint_2873 c row,
    constraint_2874 c row,
    constraint_2875 c row,
    constraint_2876 c row,
    constraint_2877 c row,
    constraint_2878 c row,
    constraint_2879 c row,
    constraint_2880 c row,
    constraint_2881 c row,
    constraint_2882 c row,
    constraint_2883 c row,
    constraint_2884 c row,
    constraint_2885 c row,
    constraint_2886 c row,
    constraint_2887 c row,
    constraint_2888 c row,
    constraint_2889 c row,
    constraint_2890 c row,
    constraint_2891 c row,
    constraint_2892 c row,
    constraint_2893 c row,
    constraint_2894 c row,
    constraint_2895 c row,
    constraint_2896 c row,
    constraint_2897 c row,
    constraint_2898 c row,
    constraint_2899 c row,
    constraint_2900 c row,
    constraint_2901 c row,
    constraint_2902 c row,
    constraint_2903 c row,
    constraint_2904 c row,
    constraint_2905 c row,
    constraint_2906 c row,
    constraint_2907 c row,
    constraint_2908 c row,
    constraint_2909 c row
  ]

-- Chi (100 items)
def seg_E_chi
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2910 c row,
    constraint_2911 c row,
    constraint_2912 c row,
    constraint_2913 c row,
    constraint_2914 c row,
    constraint_2915 c row,
    constraint_2916 c row,
    constraint_2917 c row,
    constraint_2918 c row,
    constraint_2919 c row,
    constraint_2920 c row,
    constraint_2921 c row,
    constraint_2922 c row,
    constraint_2923 c row,
    constraint_2924 c row,
    constraint_2925 c row,
    constraint_2926 c row,
    constraint_2927 c row,
    constraint_2928 c row,
    constraint_2929 c row,
    constraint_2930 c row,
    constraint_2931 c row,
    constraint_2932 c row,
    constraint_2933 c row,
    constraint_2934 c row,
    constraint_2935 c row,
    constraint_2936 c row,
    constraint_2937 c row,
    constraint_2938 c row,
    constraint_2939 c row,
    constraint_2940 c row,
    constraint_2941 c row,
    constraint_2942 c row,
    constraint_2943 c row,
    constraint_2944 c row,
    constraint_2945 c row,
    constraint_2946 c row,
    constraint_2947 c row,
    constraint_2948 c row,
    constraint_2949 c row,
    constraint_2950 c row,
    constraint_2951 c row,
    constraint_2952 c row,
    constraint_2953 c row,
    constraint_2954 c row,
    constraint_2955 c row,
    constraint_2956 c row,
    constraint_2957 c row,
    constraint_2958 c row,
    constraint_2959 c row,
    constraint_2960 c row,
    constraint_2961 c row,
    constraint_2962 c row,
    constraint_2963 c row,
    constraint_2964 c row,
    constraint_2965 c row,
    constraint_2966 c row,
    constraint_2967 c row,
    constraint_2968 c row,
    constraint_2969 c row,
    constraint_2970 c row,
    constraint_2971 c row,
    constraint_2972 c row,
    constraint_2973 c row,
    constraint_2974 c row,
    constraint_2975 c row,
    constraint_2976 c row,
    constraint_2977 c row,
    constraint_2978 c row,
    constraint_2979 c row,
    constraint_2980 c row,
    constraint_2981 c row,
    constraint_2982 c row,
    constraint_2983 c row,
    constraint_2984 c row,
    constraint_2985 c row,
    constraint_2986 c row,
    constraint_2987 c row,
    constraint_2988 c row,
    constraint_2989 c row,
    constraint_2990 c row,
    constraint_2991 c row,
    constraint_2992 c row,
    constraint_2993 c row,
    constraint_2994 c row,
    constraint_2995 c row,
    constraint_2996 c row,
    constraint_2997 c row,
    constraint_2998 c row,
    constraint_2999 c row,
    constraint_3000 c row,
    constraint_3001 c row,
    constraint_3002 c row,
    constraint_3003 c row,
    constraint_3004 c row,
    constraint_3005 c row,
    constraint_3006 c row,
    constraint_3007 c row,
    constraint_3008 c row,
    constraint_3009 c row
  ]

-- Iota boolean (64 items)
def seg_E_iota_bits
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_3010 c row,
    constraint_3011 c row,
    constraint_3012 c row,
    constraint_3013 c row,
    constraint_3014 c row,
    constraint_3015 c row,
    constraint_3016 c row,
    constraint_3017 c row,
    constraint_3018 c row,
    constraint_3019 c row,
    constraint_3020 c row,
    constraint_3021 c row,
    constraint_3022 c row,
    constraint_3023 c row,
    constraint_3024 c row,
    constraint_3025 c row,
    constraint_3026 c row,
    constraint_3027 c row,
    constraint_3028 c row,
    constraint_3029 c row,
    constraint_3030 c row,
    constraint_3031 c row,
    constraint_3032 c row,
    constraint_3033 c row,
    constraint_3034 c row,
    constraint_3035 c row,
    constraint_3036 c row,
    constraint_3037 c row,
    constraint_3038 c row,
    constraint_3039 c row,
    constraint_3040 c row,
    constraint_3041 c row,
    constraint_3042 c row,
    constraint_3043 c row,
    constraint_3044 c row,
    constraint_3045 c row,
    constraint_3046 c row,
    constraint_3047 c row,
    constraint_3048 c row,
    constraint_3049 c row,
    constraint_3050 c row,
    constraint_3051 c row,
    constraint_3052 c row,
    constraint_3053 c row,
    constraint_3054 c row,
    constraint_3055 c row,
    constraint_3056 c row,
    constraint_3057 c row,
    constraint_3058 c row,
    constraint_3059 c row,
    constraint_3060 c row,
    constraint_3061 c row,
    constraint_3062 c row,
    constraint_3063 c row,
    constraint_3064 c row,
    constraint_3065 c row,
    constraint_3066 c row,
    constraint_3067 c row,
    constraint_3068 c row,
    constraint_3069 c row,
    constraint_3070 c row,
    constraint_3071 c row,
    constraint_3072 c row,
    constraint_3073 c row
  ]

-- Iota recompose (4 items)
def seg_E_iota_recomp
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_3074 c row,
    constraint_3075 c row,
    constraint_3076 c row,
    constraint_3077 c row
  ]

-- Iota output (4 items)
def seg_E_iota_out
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_3078 c row,
    constraint_3079 c row,
    constraint_3080 c row,
    constraint_3081 c row
  ]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_eq_parts
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E c row =
      seg_E_header c row ++
      seg_E_cbits c row ++
      seg_E_cprime c row ++
      seg_E_ap_0 c row ++
      seg_E_ap_1 c row ++
      seg_E_ap_2 c row ++
      seg_E_ap_3 c row ++
      seg_E_ap_4 c row ++
      seg_E_parity c row ++
      seg_E_chi c row ++
      seg_E_iota_bits c row ++
      seg_E_iota_recomp c row ++
      seg_E_iota_out c row := by rfl

lemma seg_E_forall_parts
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    List.Forall id (seg_E_header c row) ∧
    List.Forall id (seg_E_cbits c row) ∧
    List.Forall id (seg_E_cprime c row) ∧
    List.Forall id (seg_E_ap_0 c row) ∧
    List.Forall id (seg_E_ap_1 c row) ∧
    List.Forall id (seg_E_ap_2 c row) ∧
    List.Forall id (seg_E_ap_3 c row) ∧
    List.Forall id (seg_E_ap_4 c row) ∧
    List.Forall id (seg_E_parity c row) ∧
    List.Forall id (seg_E_chi c row) ∧
    List.Forall id (seg_E_iota_bits c row) ∧
    List.Forall id (seg_E_iota_recomp c row) ∧
    List.Forall id (seg_E_iota_out c row) := by
  rw [seg_E_eq_parts] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h_hdr, h_cb⟩, h_cp⟩, h_a0⟩, h_a1⟩, h_a2⟩, h_a3⟩, h_a4⟩, h_pa⟩, h_ch⟩,
    h_ib⟩, h_ir⟩, h_io⟩ := h
  exact ⟨h_hdr, h_cb, h_cp, h_a0, h_a1, h_a2, h_a3, h_a4, h_pa, h_ch, h_ib, h_ir, h_io⟩

-- CBits chunk 0 (64 items, constraints 250-313)
def seg_E_cbits_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_250 c row,
    constraint_251 c row,
    constraint_252 c row,
    constraint_253 c row,
    constraint_254 c row,
    constraint_255 c row,
    constraint_256 c row,
    constraint_257 c row,
    constraint_258 c row,
    constraint_259 c row,
    constraint_260 c row,
    constraint_261 c row,
    constraint_262 c row,
    constraint_263 c row,
    constraint_264 c row,
    constraint_265 c row,
    constraint_266 c row,
    constraint_267 c row,
    constraint_268 c row,
    constraint_269 c row,
    constraint_270 c row,
    constraint_271 c row,
    constraint_272 c row,
    constraint_273 c row,
    constraint_274 c row,
    constraint_275 c row,
    constraint_276 c row,
    constraint_277 c row,
    constraint_278 c row,
    constraint_279 c row,
    constraint_280 c row,
    constraint_281 c row,
    constraint_282 c row,
    constraint_283 c row,
    constraint_284 c row,
    constraint_285 c row,
    constraint_286 c row,
    constraint_287 c row,
    constraint_288 c row,
    constraint_289 c row,
    constraint_290 c row,
    constraint_291 c row,
    constraint_292 c row,
    constraint_293 c row,
    constraint_294 c row,
    constraint_295 c row,
    constraint_296 c row,
    constraint_297 c row,
    constraint_298 c row,
    constraint_299 c row,
    constraint_300 c row,
    constraint_301 c row,
    constraint_302 c row,
    constraint_303 c row,
    constraint_304 c row,
    constraint_305 c row,
    constraint_306 c row,
    constraint_307 c row,
    constraint_308 c row,
    constraint_309 c row,
    constraint_310 c row,
    constraint_311 c row,
    constraint_312 c row,
    constraint_313 c row
  ]

-- CBits chunk 1 (64 items, constraints 314-377)
def seg_E_cbits_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_314 c row,
    constraint_315 c row,
    constraint_316 c row,
    constraint_317 c row,
    constraint_318 c row,
    constraint_319 c row,
    constraint_320 c row,
    constraint_321 c row,
    constraint_322 c row,
    constraint_323 c row,
    constraint_324 c row,
    constraint_325 c row,
    constraint_326 c row,
    constraint_327 c row,
    constraint_328 c row,
    constraint_329 c row,
    constraint_330 c row,
    constraint_331 c row,
    constraint_332 c row,
    constraint_333 c row,
    constraint_334 c row,
    constraint_335 c row,
    constraint_336 c row,
    constraint_337 c row,
    constraint_338 c row,
    constraint_339 c row,
    constraint_340 c row,
    constraint_341 c row,
    constraint_342 c row,
    constraint_343 c row,
    constraint_344 c row,
    constraint_345 c row,
    constraint_346 c row,
    constraint_347 c row,
    constraint_348 c row,
    constraint_349 c row,
    constraint_350 c row,
    constraint_351 c row,
    constraint_352 c row,
    constraint_353 c row,
    constraint_354 c row,
    constraint_355 c row,
    constraint_356 c row,
    constraint_357 c row,
    constraint_358 c row,
    constraint_359 c row,
    constraint_360 c row,
    constraint_361 c row,
    constraint_362 c row,
    constraint_363 c row,
    constraint_364 c row,
    constraint_365 c row,
    constraint_366 c row,
    constraint_367 c row,
    constraint_368 c row,
    constraint_369 c row,
    constraint_370 c row,
    constraint_371 c row,
    constraint_372 c row,
    constraint_373 c row,
    constraint_374 c row,
    constraint_375 c row,
    constraint_376 c row,
    constraint_377 c row
  ]

-- CBits chunk 2 (64 items, constraints 378-441)
def seg_E_cbits_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_378 c row,
    constraint_379 c row,
    constraint_380 c row,
    constraint_381 c row,
    constraint_382 c row,
    constraint_383 c row,
    constraint_384 c row,
    constraint_385 c row,
    constraint_386 c row,
    constraint_387 c row,
    constraint_388 c row,
    constraint_389 c row,
    constraint_390 c row,
    constraint_391 c row,
    constraint_392 c row,
    constraint_393 c row,
    constraint_394 c row,
    constraint_395 c row,
    constraint_396 c row,
    constraint_397 c row,
    constraint_398 c row,
    constraint_399 c row,
    constraint_400 c row,
    constraint_401 c row,
    constraint_402 c row,
    constraint_403 c row,
    constraint_404 c row,
    constraint_405 c row,
    constraint_406 c row,
    constraint_407 c row,
    constraint_408 c row,
    constraint_409 c row,
    constraint_410 c row,
    constraint_411 c row,
    constraint_412 c row,
    constraint_413 c row,
    constraint_414 c row,
    constraint_415 c row,
    constraint_416 c row,
    constraint_417 c row,
    constraint_418 c row,
    constraint_419 c row,
    constraint_420 c row,
    constraint_421 c row,
    constraint_422 c row,
    constraint_423 c row,
    constraint_424 c row,
    constraint_425 c row,
    constraint_426 c row,
    constraint_427 c row,
    constraint_428 c row,
    constraint_429 c row,
    constraint_430 c row,
    constraint_431 c row,
    constraint_432 c row,
    constraint_433 c row,
    constraint_434 c row,
    constraint_435 c row,
    constraint_436 c row,
    constraint_437 c row,
    constraint_438 c row,
    constraint_439 c row,
    constraint_440 c row,
    constraint_441 c row
  ]

-- CBits chunk 3 (64 items, constraints 442-505)
def seg_E_cbits_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_442 c row,
    constraint_443 c row,
    constraint_444 c row,
    constraint_445 c row,
    constraint_446 c row,
    constraint_447 c row,
    constraint_448 c row,
    constraint_449 c row,
    constraint_450 c row,
    constraint_451 c row,
    constraint_452 c row,
    constraint_453 c row,
    constraint_454 c row,
    constraint_455 c row,
    constraint_456 c row,
    constraint_457 c row,
    constraint_458 c row,
    constraint_459 c row,
    constraint_460 c row,
    constraint_461 c row,
    constraint_462 c row,
    constraint_463 c row,
    constraint_464 c row,
    constraint_465 c row,
    constraint_466 c row,
    constraint_467 c row,
    constraint_468 c row,
    constraint_469 c row,
    constraint_470 c row,
    constraint_471 c row,
    constraint_472 c row,
    constraint_473 c row,
    constraint_474 c row,
    constraint_475 c row,
    constraint_476 c row,
    constraint_477 c row,
    constraint_478 c row,
    constraint_479 c row,
    constraint_480 c row,
    constraint_481 c row,
    constraint_482 c row,
    constraint_483 c row,
    constraint_484 c row,
    constraint_485 c row,
    constraint_486 c row,
    constraint_487 c row,
    constraint_488 c row,
    constraint_489 c row,
    constraint_490 c row,
    constraint_491 c row,
    constraint_492 c row,
    constraint_493 c row,
    constraint_494 c row,
    constraint_495 c row,
    constraint_496 c row,
    constraint_497 c row,
    constraint_498 c row,
    constraint_499 c row,
    constraint_500 c row,
    constraint_501 c row,
    constraint_502 c row,
    constraint_503 c row,
    constraint_504 c row,
    constraint_505 c row
  ]

-- CBits chunk 4 (64 items, constraints 506-569)
def seg_E_cbits_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_506 c row,
    constraint_507 c row,
    constraint_508 c row,
    constraint_509 c row,
    constraint_510 c row,
    constraint_511 c row,
    constraint_512 c row,
    constraint_513 c row,
    constraint_514 c row,
    constraint_515 c row,
    constraint_516 c row,
    constraint_517 c row,
    constraint_518 c row,
    constraint_519 c row,
    constraint_520 c row,
    constraint_521 c row,
    constraint_522 c row,
    constraint_523 c row,
    constraint_524 c row,
    constraint_525 c row,
    constraint_526 c row,
    constraint_527 c row,
    constraint_528 c row,
    constraint_529 c row,
    constraint_530 c row,
    constraint_531 c row,
    constraint_532 c row,
    constraint_533 c row,
    constraint_534 c row,
    constraint_535 c row,
    constraint_536 c row,
    constraint_537 c row,
    constraint_538 c row,
    constraint_539 c row,
    constraint_540 c row,
    constraint_541 c row,
    constraint_542 c row,
    constraint_543 c row,
    constraint_544 c row,
    constraint_545 c row,
    constraint_546 c row,
    constraint_547 c row,
    constraint_548 c row,
    constraint_549 c row,
    constraint_550 c row,
    constraint_551 c row,
    constraint_552 c row,
    constraint_553 c row,
    constraint_554 c row,
    constraint_555 c row,
    constraint_556 c row,
    constraint_557 c row,
    constraint_558 c row,
    constraint_559 c row,
    constraint_560 c row,
    constraint_561 c row,
    constraint_562 c row,
    constraint_563 c row,
    constraint_564 c row,
    constraint_565 c row,
    constraint_566 c row,
    constraint_567 c row,
    constraint_568 c row,
    constraint_569 c row
  ]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 65536 in
lemma seg_E_cbits_eq_chunks
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_cbits c row =
      seg_E_cbits_0 c row ++
      seg_E_cbits_1 c row ++
      seg_E_cbits_2 c row ++
      seg_E_cbits_3 c row ++
      seg_E_cbits_4 c row := by rfl

-- CPrime chunk 0 (64 items, constraints 570-633)
def seg_E_cprime_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_570 c row,
    constraint_571 c row,
    constraint_572 c row,
    constraint_573 c row,
    constraint_574 c row,
    constraint_575 c row,
    constraint_576 c row,
    constraint_577 c row,
    constraint_578 c row,
    constraint_579 c row,
    constraint_580 c row,
    constraint_581 c row,
    constraint_582 c row,
    constraint_583 c row,
    constraint_584 c row,
    constraint_585 c row,
    constraint_586 c row,
    constraint_587 c row,
    constraint_588 c row,
    constraint_589 c row,
    constraint_590 c row,
    constraint_591 c row,
    constraint_592 c row,
    constraint_593 c row,
    constraint_594 c row,
    constraint_595 c row,
    constraint_596 c row,
    constraint_597 c row,
    constraint_598 c row,
    constraint_599 c row,
    constraint_600 c row,
    constraint_601 c row,
    constraint_602 c row,
    constraint_603 c row,
    constraint_604 c row,
    constraint_605 c row,
    constraint_606 c row,
    constraint_607 c row,
    constraint_608 c row,
    constraint_609 c row,
    constraint_610 c row,
    constraint_611 c row,
    constraint_612 c row,
    constraint_613 c row,
    constraint_614 c row,
    constraint_615 c row,
    constraint_616 c row,
    constraint_617 c row,
    constraint_618 c row,
    constraint_619 c row,
    constraint_620 c row,
    constraint_621 c row,
    constraint_622 c row,
    constraint_623 c row,
    constraint_624 c row,
    constraint_625 c row,
    constraint_626 c row,
    constraint_627 c row,
    constraint_628 c row,
    constraint_629 c row,
    constraint_630 c row,
    constraint_631 c row,
    constraint_632 c row,
    constraint_633 c row
  ]

-- CPrime chunk 1 (64 items, constraints 634-697)
def seg_E_cprime_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_634 c row,
    constraint_635 c row,
    constraint_636 c row,
    constraint_637 c row,
    constraint_638 c row,
    constraint_639 c row,
    constraint_640 c row,
    constraint_641 c row,
    constraint_642 c row,
    constraint_643 c row,
    constraint_644 c row,
    constraint_645 c row,
    constraint_646 c row,
    constraint_647 c row,
    constraint_648 c row,
    constraint_649 c row,
    constraint_650 c row,
    constraint_651 c row,
    constraint_652 c row,
    constraint_653 c row,
    constraint_654 c row,
    constraint_655 c row,
    constraint_656 c row,
    constraint_657 c row,
    constraint_658 c row,
    constraint_659 c row,
    constraint_660 c row,
    constraint_661 c row,
    constraint_662 c row,
    constraint_663 c row,
    constraint_664 c row,
    constraint_665 c row,
    constraint_666 c row,
    constraint_667 c row,
    constraint_668 c row,
    constraint_669 c row,
    constraint_670 c row,
    constraint_671 c row,
    constraint_672 c row,
    constraint_673 c row,
    constraint_674 c row,
    constraint_675 c row,
    constraint_676 c row,
    constraint_677 c row,
    constraint_678 c row,
    constraint_679 c row,
    constraint_680 c row,
    constraint_681 c row,
    constraint_682 c row,
    constraint_683 c row,
    constraint_684 c row,
    constraint_685 c row,
    constraint_686 c row,
    constraint_687 c row,
    constraint_688 c row,
    constraint_689 c row,
    constraint_690 c row,
    constraint_691 c row,
    constraint_692 c row,
    constraint_693 c row,
    constraint_694 c row,
    constraint_695 c row,
    constraint_696 c row,
    constraint_697 c row
  ]

-- CPrime chunk 2 (64 items, constraints 698-761)
def seg_E_cprime_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_698 c row,
    constraint_699 c row,
    constraint_700 c row,
    constraint_701 c row,
    constraint_702 c row,
    constraint_703 c row,
    constraint_704 c row,
    constraint_705 c row,
    constraint_706 c row,
    constraint_707 c row,
    constraint_708 c row,
    constraint_709 c row,
    constraint_710 c row,
    constraint_711 c row,
    constraint_712 c row,
    constraint_713 c row,
    constraint_714 c row,
    constraint_715 c row,
    constraint_716 c row,
    constraint_717 c row,
    constraint_718 c row,
    constraint_719 c row,
    constraint_720 c row,
    constraint_721 c row,
    constraint_722 c row,
    constraint_723 c row,
    constraint_724 c row,
    constraint_725 c row,
    constraint_726 c row,
    constraint_727 c row,
    constraint_728 c row,
    constraint_729 c row,
    constraint_730 c row,
    constraint_731 c row,
    constraint_732 c row,
    constraint_733 c row,
    constraint_734 c row,
    constraint_735 c row,
    constraint_736 c row,
    constraint_737 c row,
    constraint_738 c row,
    constraint_739 c row,
    constraint_740 c row,
    constraint_741 c row,
    constraint_742 c row,
    constraint_743 c row,
    constraint_744 c row,
    constraint_745 c row,
    constraint_746 c row,
    constraint_747 c row,
    constraint_748 c row,
    constraint_749 c row,
    constraint_750 c row,
    constraint_751 c row,
    constraint_752 c row,
    constraint_753 c row,
    constraint_754 c row,
    constraint_755 c row,
    constraint_756 c row,
    constraint_757 c row,
    constraint_758 c row,
    constraint_759 c row,
    constraint_760 c row,
    constraint_761 c row
  ]

-- CPrime chunk 3 (64 items, constraints 762-825)
def seg_E_cprime_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_762 c row,
    constraint_763 c row,
    constraint_764 c row,
    constraint_765 c row,
    constraint_766 c row,
    constraint_767 c row,
    constraint_768 c row,
    constraint_769 c row,
    constraint_770 c row,
    constraint_771 c row,
    constraint_772 c row,
    constraint_773 c row,
    constraint_774 c row,
    constraint_775 c row,
    constraint_776 c row,
    constraint_777 c row,
    constraint_778 c row,
    constraint_779 c row,
    constraint_780 c row,
    constraint_781 c row,
    constraint_782 c row,
    constraint_783 c row,
    constraint_784 c row,
    constraint_785 c row,
    constraint_786 c row,
    constraint_787 c row,
    constraint_788 c row,
    constraint_789 c row,
    constraint_790 c row,
    constraint_791 c row,
    constraint_792 c row,
    constraint_793 c row,
    constraint_794 c row,
    constraint_795 c row,
    constraint_796 c row,
    constraint_797 c row,
    constraint_798 c row,
    constraint_799 c row,
    constraint_800 c row,
    constraint_801 c row,
    constraint_802 c row,
    constraint_803 c row,
    constraint_804 c row,
    constraint_805 c row,
    constraint_806 c row,
    constraint_807 c row,
    constraint_808 c row,
    constraint_809 c row,
    constraint_810 c row,
    constraint_811 c row,
    constraint_812 c row,
    constraint_813 c row,
    constraint_814 c row,
    constraint_815 c row,
    constraint_816 c row,
    constraint_817 c row,
    constraint_818 c row,
    constraint_819 c row,
    constraint_820 c row,
    constraint_821 c row,
    constraint_822 c row,
    constraint_823 c row,
    constraint_824 c row,
    constraint_825 c row
  ]

-- CPrime chunk 4 (64 items, constraints 826-889)
def seg_E_cprime_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_826 c row,
    constraint_827 c row,
    constraint_828 c row,
    constraint_829 c row,
    constraint_830 c row,
    constraint_831 c row,
    constraint_832 c row,
    constraint_833 c row,
    constraint_834 c row,
    constraint_835 c row,
    constraint_836 c row,
    constraint_837 c row,
    constraint_838 c row,
    constraint_839 c row,
    constraint_840 c row,
    constraint_841 c row,
    constraint_842 c row,
    constraint_843 c row,
    constraint_844 c row,
    constraint_845 c row,
    constraint_846 c row,
    constraint_847 c row,
    constraint_848 c row,
    constraint_849 c row,
    constraint_850 c row,
    constraint_851 c row,
    constraint_852 c row,
    constraint_853 c row,
    constraint_854 c row,
    constraint_855 c row,
    constraint_856 c row,
    constraint_857 c row,
    constraint_858 c row,
    constraint_859 c row,
    constraint_860 c row,
    constraint_861 c row,
    constraint_862 c row,
    constraint_863 c row,
    constraint_864 c row,
    constraint_865 c row,
    constraint_866 c row,
    constraint_867 c row,
    constraint_868 c row,
    constraint_869 c row,
    constraint_870 c row,
    constraint_871 c row,
    constraint_872 c row,
    constraint_873 c row,
    constraint_874 c row,
    constraint_875 c row,
    constraint_876 c row,
    constraint_877 c row,
    constraint_878 c row,
    constraint_879 c row,
    constraint_880 c row,
    constraint_881 c row,
    constraint_882 c row,
    constraint_883 c row,
    constraint_884 c row,
    constraint_885 c row,
    constraint_886 c row,
    constraint_887 c row,
    constraint_888 c row,
    constraint_889 c row
  ]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 65536 in
lemma seg_E_cprime_eq_chunks
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_cprime c row =
      seg_E_cprime_0 c row ++
      seg_E_cprime_1 c row ++
      seg_E_cprime_2 c row ++
      seg_E_cprime_3 c row ++
      seg_E_cprime_4 c row := by rfl

-- APrime group 0 block 0 booleans (64 items)
def seg_E_ap_0_bool_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_890 c row,
    constraint_891 c row,
    constraint_892 c row,
    constraint_893 c row,
    constraint_894 c row,
    constraint_895 c row,
    constraint_896 c row,
    constraint_897 c row,
    constraint_898 c row,
    constraint_899 c row,
    constraint_900 c row,
    constraint_901 c row,
    constraint_902 c row,
    constraint_903 c row,
    constraint_904 c row,
    constraint_905 c row,
    constraint_906 c row,
    constraint_907 c row,
    constraint_908 c row,
    constraint_909 c row,
    constraint_910 c row,
    constraint_911 c row,
    constraint_912 c row,
    constraint_913 c row,
    constraint_914 c row,
    constraint_915 c row,
    constraint_916 c row,
    constraint_917 c row,
    constraint_918 c row,
    constraint_919 c row,
    constraint_920 c row,
    constraint_921 c row,
    constraint_922 c row,
    constraint_923 c row,
    constraint_924 c row,
    constraint_925 c row,
    constraint_926 c row,
    constraint_927 c row,
    constraint_928 c row,
    constraint_929 c row,
    constraint_930 c row,
    constraint_931 c row,
    constraint_932 c row,
    constraint_933 c row,
    constraint_934 c row,
    constraint_935 c row,
    constraint_936 c row,
    constraint_937 c row,
    constraint_938 c row,
    constraint_939 c row,
    constraint_940 c row,
    constraint_941 c row,
    constraint_942 c row,
    constraint_943 c row,
    constraint_944 c row,
    constraint_945 c row,
    constraint_946 c row,
    constraint_947 c row,
    constraint_948 c row,
    constraint_949 c row,
    constraint_950 c row,
    constraint_951 c row,
    constraint_952 c row,
    constraint_953 c row
  ]

-- APrime group 0 block 0 xor3 (4 items)
def seg_E_ap_0_xor3_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_954 c row,
    constraint_955 c row,
    constraint_956 c row,
    constraint_957 c row
  ]

-- APrime group 0 block 1 booleans (64 items)
def seg_E_ap_0_bool_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_958 c row,
    constraint_959 c row,
    constraint_960 c row,
    constraint_961 c row,
    constraint_962 c row,
    constraint_963 c row,
    constraint_964 c row,
    constraint_965 c row,
    constraint_966 c row,
    constraint_967 c row,
    constraint_968 c row,
    constraint_969 c row,
    constraint_970 c row,
    constraint_971 c row,
    constraint_972 c row,
    constraint_973 c row,
    constraint_974 c row,
    constraint_975 c row,
    constraint_976 c row,
    constraint_977 c row,
    constraint_978 c row,
    constraint_979 c row,
    constraint_980 c row,
    constraint_981 c row,
    constraint_982 c row,
    constraint_983 c row,
    constraint_984 c row,
    constraint_985 c row,
    constraint_986 c row,
    constraint_987 c row,
    constraint_988 c row,
    constraint_989 c row,
    constraint_990 c row,
    constraint_991 c row,
    constraint_992 c row,
    constraint_993 c row,
    constraint_994 c row,
    constraint_995 c row,
    constraint_996 c row,
    constraint_997 c row,
    constraint_998 c row,
    constraint_999 c row,
    constraint_1000 c row,
    constraint_1001 c row,
    constraint_1002 c row,
    constraint_1003 c row,
    constraint_1004 c row,
    constraint_1005 c row,
    constraint_1006 c row,
    constraint_1007 c row,
    constraint_1008 c row,
    constraint_1009 c row,
    constraint_1010 c row,
    constraint_1011 c row,
    constraint_1012 c row,
    constraint_1013 c row,
    constraint_1014 c row,
    constraint_1015 c row,
    constraint_1016 c row,
    constraint_1017 c row,
    constraint_1018 c row,
    constraint_1019 c row,
    constraint_1020 c row,
    constraint_1021 c row
  ]

-- APrime group 0 block 1 xor3 (4 items)
def seg_E_ap_0_xor3_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1022 c row,
    constraint_1023 c row,
    constraint_1024 c row,
    constraint_1025 c row
  ]

-- APrime group 0 block 2 booleans (64 items)
def seg_E_ap_0_bool_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1026 c row,
    constraint_1027 c row,
    constraint_1028 c row,
    constraint_1029 c row,
    constraint_1030 c row,
    constraint_1031 c row,
    constraint_1032 c row,
    constraint_1033 c row,
    constraint_1034 c row,
    constraint_1035 c row,
    constraint_1036 c row,
    constraint_1037 c row,
    constraint_1038 c row,
    constraint_1039 c row,
    constraint_1040 c row,
    constraint_1041 c row,
    constraint_1042 c row,
    constraint_1043 c row,
    constraint_1044 c row,
    constraint_1045 c row,
    constraint_1046 c row,
    constraint_1047 c row,
    constraint_1048 c row,
    constraint_1049 c row,
    constraint_1050 c row,
    constraint_1051 c row,
    constraint_1052 c row,
    constraint_1053 c row,
    constraint_1054 c row,
    constraint_1055 c row,
    constraint_1056 c row,
    constraint_1057 c row,
    constraint_1058 c row,
    constraint_1059 c row,
    constraint_1060 c row,
    constraint_1061 c row,
    constraint_1062 c row,
    constraint_1063 c row,
    constraint_1064 c row,
    constraint_1065 c row,
    constraint_1066 c row,
    constraint_1067 c row,
    constraint_1068 c row,
    constraint_1069 c row,
    constraint_1070 c row,
    constraint_1071 c row,
    constraint_1072 c row,
    constraint_1073 c row,
    constraint_1074 c row,
    constraint_1075 c row,
    constraint_1076 c row,
    constraint_1077 c row,
    constraint_1078 c row,
    constraint_1079 c row,
    constraint_1080 c row,
    constraint_1081 c row,
    constraint_1082 c row,
    constraint_1083 c row,
    constraint_1084 c row,
    constraint_1085 c row,
    constraint_1086 c row,
    constraint_1087 c row,
    constraint_1088 c row,
    constraint_1089 c row
  ]

-- APrime group 0 block 2 xor3 (4 items)
def seg_E_ap_0_xor3_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1090 c row,
    constraint_1091 c row,
    constraint_1092 c row,
    constraint_1093 c row
  ]

-- APrime group 0 block 3 booleans (64 items)
def seg_E_ap_0_bool_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1094 c row,
    constraint_1095 c row,
    constraint_1096 c row,
    constraint_1097 c row,
    constraint_1098 c row,
    constraint_1099 c row,
    constraint_1100 c row,
    constraint_1101 c row,
    constraint_1102 c row,
    constraint_1103 c row,
    constraint_1104 c row,
    constraint_1105 c row,
    constraint_1106 c row,
    constraint_1107 c row,
    constraint_1108 c row,
    constraint_1109 c row,
    constraint_1110 c row,
    constraint_1111 c row,
    constraint_1112 c row,
    constraint_1113 c row,
    constraint_1114 c row,
    constraint_1115 c row,
    constraint_1116 c row,
    constraint_1117 c row,
    constraint_1118 c row,
    constraint_1119 c row,
    constraint_1120 c row,
    constraint_1121 c row,
    constraint_1122 c row,
    constraint_1123 c row,
    constraint_1124 c row,
    constraint_1125 c row,
    constraint_1126 c row,
    constraint_1127 c row,
    constraint_1128 c row,
    constraint_1129 c row,
    constraint_1130 c row,
    constraint_1131 c row,
    constraint_1132 c row,
    constraint_1133 c row,
    constraint_1134 c row,
    constraint_1135 c row,
    constraint_1136 c row,
    constraint_1137 c row,
    constraint_1138 c row,
    constraint_1139 c row,
    constraint_1140 c row,
    constraint_1141 c row,
    constraint_1142 c row,
    constraint_1143 c row,
    constraint_1144 c row,
    constraint_1145 c row,
    constraint_1146 c row,
    constraint_1147 c row,
    constraint_1148 c row,
    constraint_1149 c row,
    constraint_1150 c row,
    constraint_1151 c row,
    constraint_1152 c row,
    constraint_1153 c row,
    constraint_1154 c row,
    constraint_1155 c row,
    constraint_1156 c row,
    constraint_1157 c row
  ]

-- APrime group 0 block 3 xor3 (4 items)
def seg_E_ap_0_xor3_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1158 c row,
    constraint_1159 c row,
    constraint_1160 c row,
    constraint_1161 c row
  ]

-- APrime group 0 block 4 booleans (64 items)
def seg_E_ap_0_bool_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1162 c row,
    constraint_1163 c row,
    constraint_1164 c row,
    constraint_1165 c row,
    constraint_1166 c row,
    constraint_1167 c row,
    constraint_1168 c row,
    constraint_1169 c row,
    constraint_1170 c row,
    constraint_1171 c row,
    constraint_1172 c row,
    constraint_1173 c row,
    constraint_1174 c row,
    constraint_1175 c row,
    constraint_1176 c row,
    constraint_1177 c row,
    constraint_1178 c row,
    constraint_1179 c row,
    constraint_1180 c row,
    constraint_1181 c row,
    constraint_1182 c row,
    constraint_1183 c row,
    constraint_1184 c row,
    constraint_1185 c row,
    constraint_1186 c row,
    constraint_1187 c row,
    constraint_1188 c row,
    constraint_1189 c row,
    constraint_1190 c row,
    constraint_1191 c row,
    constraint_1192 c row,
    constraint_1193 c row,
    constraint_1194 c row,
    constraint_1195 c row,
    constraint_1196 c row,
    constraint_1197 c row,
    constraint_1198 c row,
    constraint_1199 c row,
    constraint_1200 c row,
    constraint_1201 c row,
    constraint_1202 c row,
    constraint_1203 c row,
    constraint_1204 c row,
    constraint_1205 c row,
    constraint_1206 c row,
    constraint_1207 c row,
    constraint_1208 c row,
    constraint_1209 c row,
    constraint_1210 c row,
    constraint_1211 c row,
    constraint_1212 c row,
    constraint_1213 c row,
    constraint_1214 c row,
    constraint_1215 c row,
    constraint_1216 c row,
    constraint_1217 c row,
    constraint_1218 c row,
    constraint_1219 c row,
    constraint_1220 c row,
    constraint_1221 c row,
    constraint_1222 c row,
    constraint_1223 c row,
    constraint_1224 c row,
    constraint_1225 c row
  ]

-- APrime group 0 block 4 xor3 (4 items)
def seg_E_ap_0_xor3_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1226 c row,
    constraint_1227 c row,
    constraint_1228 c row,
    constraint_1229 c row
  ]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 65536 in
lemma seg_E_ap_0_eq_chunks
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0 c row =
      seg_E_ap_0_bool_0 c row ++
      seg_E_ap_0_xor3_0 c row ++
      seg_E_ap_0_bool_1 c row ++
      seg_E_ap_0_xor3_1 c row ++
      seg_E_ap_0_bool_2 c row ++
      seg_E_ap_0_xor3_2 c row ++
      seg_E_ap_0_bool_3 c row ++
      seg_E_ap_0_xor3_3 c row ++
      seg_E_ap_0_bool_4 c row ++
      seg_E_ap_0_xor3_4 c row := by rfl

-- APrime group 1 block 0 booleans (64 items)
def seg_E_ap_1_bool_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1230 c row,
    constraint_1231 c row,
    constraint_1232 c row,
    constraint_1233 c row,
    constraint_1234 c row,
    constraint_1235 c row,
    constraint_1236 c row,
    constraint_1237 c row,
    constraint_1238 c row,
    constraint_1239 c row,
    constraint_1240 c row,
    constraint_1241 c row,
    constraint_1242 c row,
    constraint_1243 c row,
    constraint_1244 c row,
    constraint_1245 c row,
    constraint_1246 c row,
    constraint_1247 c row,
    constraint_1248 c row,
    constraint_1249 c row,
    constraint_1250 c row,
    constraint_1251 c row,
    constraint_1252 c row,
    constraint_1253 c row,
    constraint_1254 c row,
    constraint_1255 c row,
    constraint_1256 c row,
    constraint_1257 c row,
    constraint_1258 c row,
    constraint_1259 c row,
    constraint_1260 c row,
    constraint_1261 c row,
    constraint_1262 c row,
    constraint_1263 c row,
    constraint_1264 c row,
    constraint_1265 c row,
    constraint_1266 c row,
    constraint_1267 c row,
    constraint_1268 c row,
    constraint_1269 c row,
    constraint_1270 c row,
    constraint_1271 c row,
    constraint_1272 c row,
    constraint_1273 c row,
    constraint_1274 c row,
    constraint_1275 c row,
    constraint_1276 c row,
    constraint_1277 c row,
    constraint_1278 c row,
    constraint_1279 c row,
    constraint_1280 c row,
    constraint_1281 c row,
    constraint_1282 c row,
    constraint_1283 c row,
    constraint_1284 c row,
    constraint_1285 c row,
    constraint_1286 c row,
    constraint_1287 c row,
    constraint_1288 c row,
    constraint_1289 c row,
    constraint_1290 c row,
    constraint_1291 c row,
    constraint_1292 c row,
    constraint_1293 c row
  ]

-- APrime group 1 block 0 xor3 (4 items)
def seg_E_ap_1_xor3_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1294 c row,
    constraint_1295 c row,
    constraint_1296 c row,
    constraint_1297 c row
  ]

-- APrime group 1 block 1 booleans (64 items)
def seg_E_ap_1_bool_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1298 c row,
    constraint_1299 c row,
    constraint_1300 c row,
    constraint_1301 c row,
    constraint_1302 c row,
    constraint_1303 c row,
    constraint_1304 c row,
    constraint_1305 c row,
    constraint_1306 c row,
    constraint_1307 c row,
    constraint_1308 c row,
    constraint_1309 c row,
    constraint_1310 c row,
    constraint_1311 c row,
    constraint_1312 c row,
    constraint_1313 c row,
    constraint_1314 c row,
    constraint_1315 c row,
    constraint_1316 c row,
    constraint_1317 c row,
    constraint_1318 c row,
    constraint_1319 c row,
    constraint_1320 c row,
    constraint_1321 c row,
    constraint_1322 c row,
    constraint_1323 c row,
    constraint_1324 c row,
    constraint_1325 c row,
    constraint_1326 c row,
    constraint_1327 c row,
    constraint_1328 c row,
    constraint_1329 c row,
    constraint_1330 c row,
    constraint_1331 c row,
    constraint_1332 c row,
    constraint_1333 c row,
    constraint_1334 c row,
    constraint_1335 c row,
    constraint_1336 c row,
    constraint_1337 c row,
    constraint_1338 c row,
    constraint_1339 c row,
    constraint_1340 c row,
    constraint_1341 c row,
    constraint_1342 c row,
    constraint_1343 c row,
    constraint_1344 c row,
    constraint_1345 c row,
    constraint_1346 c row,
    constraint_1347 c row,
    constraint_1348 c row,
    constraint_1349 c row,
    constraint_1350 c row,
    constraint_1351 c row,
    constraint_1352 c row,
    constraint_1353 c row,
    constraint_1354 c row,
    constraint_1355 c row,
    constraint_1356 c row,
    constraint_1357 c row,
    constraint_1358 c row,
    constraint_1359 c row,
    constraint_1360 c row,
    constraint_1361 c row
  ]

-- APrime group 1 block 1 xor3 (4 items)
def seg_E_ap_1_xor3_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1362 c row,
    constraint_1363 c row,
    constraint_1364 c row,
    constraint_1365 c row
  ]

-- APrime group 1 block 2 booleans (64 items)
def seg_E_ap_1_bool_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1366 c row,
    constraint_1367 c row,
    constraint_1368 c row,
    constraint_1369 c row,
    constraint_1370 c row,
    constraint_1371 c row,
    constraint_1372 c row,
    constraint_1373 c row,
    constraint_1374 c row,
    constraint_1375 c row,
    constraint_1376 c row,
    constraint_1377 c row,
    constraint_1378 c row,
    constraint_1379 c row,
    constraint_1380 c row,
    constraint_1381 c row,
    constraint_1382 c row,
    constraint_1383 c row,
    constraint_1384 c row,
    constraint_1385 c row,
    constraint_1386 c row,
    constraint_1387 c row,
    constraint_1388 c row,
    constraint_1389 c row,
    constraint_1390 c row,
    constraint_1391 c row,
    constraint_1392 c row,
    constraint_1393 c row,
    constraint_1394 c row,
    constraint_1395 c row,
    constraint_1396 c row,
    constraint_1397 c row,
    constraint_1398 c row,
    constraint_1399 c row,
    constraint_1400 c row,
    constraint_1401 c row,
    constraint_1402 c row,
    constraint_1403 c row,
    constraint_1404 c row,
    constraint_1405 c row,
    constraint_1406 c row,
    constraint_1407 c row,
    constraint_1408 c row,
    constraint_1409 c row,
    constraint_1410 c row,
    constraint_1411 c row,
    constraint_1412 c row,
    constraint_1413 c row,
    constraint_1414 c row,
    constraint_1415 c row,
    constraint_1416 c row,
    constraint_1417 c row,
    constraint_1418 c row,
    constraint_1419 c row,
    constraint_1420 c row,
    constraint_1421 c row,
    constraint_1422 c row,
    constraint_1423 c row,
    constraint_1424 c row,
    constraint_1425 c row,
    constraint_1426 c row,
    constraint_1427 c row,
    constraint_1428 c row,
    constraint_1429 c row
  ]

-- APrime group 1 block 2 xor3 (4 items)
def seg_E_ap_1_xor3_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1430 c row,
    constraint_1431 c row,
    constraint_1432 c row,
    constraint_1433 c row
  ]

-- APrime group 1 block 3 booleans (64 items)
def seg_E_ap_1_bool_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1434 c row,
    constraint_1435 c row,
    constraint_1436 c row,
    constraint_1437 c row,
    constraint_1438 c row,
    constraint_1439 c row,
    constraint_1440 c row,
    constraint_1441 c row,
    constraint_1442 c row,
    constraint_1443 c row,
    constraint_1444 c row,
    constraint_1445 c row,
    constraint_1446 c row,
    constraint_1447 c row,
    constraint_1448 c row,
    constraint_1449 c row,
    constraint_1450 c row,
    constraint_1451 c row,
    constraint_1452 c row,
    constraint_1453 c row,
    constraint_1454 c row,
    constraint_1455 c row,
    constraint_1456 c row,
    constraint_1457 c row,
    constraint_1458 c row,
    constraint_1459 c row,
    constraint_1460 c row,
    constraint_1461 c row,
    constraint_1462 c row,
    constraint_1463 c row,
    constraint_1464 c row,
    constraint_1465 c row,
    constraint_1466 c row,
    constraint_1467 c row,
    constraint_1468 c row,
    constraint_1469 c row,
    constraint_1470 c row,
    constraint_1471 c row,
    constraint_1472 c row,
    constraint_1473 c row,
    constraint_1474 c row,
    constraint_1475 c row,
    constraint_1476 c row,
    constraint_1477 c row,
    constraint_1478 c row,
    constraint_1479 c row,
    constraint_1480 c row,
    constraint_1481 c row,
    constraint_1482 c row,
    constraint_1483 c row,
    constraint_1484 c row,
    constraint_1485 c row,
    constraint_1486 c row,
    constraint_1487 c row,
    constraint_1488 c row,
    constraint_1489 c row,
    constraint_1490 c row,
    constraint_1491 c row,
    constraint_1492 c row,
    constraint_1493 c row,
    constraint_1494 c row,
    constraint_1495 c row,
    constraint_1496 c row,
    constraint_1497 c row
  ]

-- APrime group 1 block 3 xor3 (4 items)
def seg_E_ap_1_xor3_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1498 c row,
    constraint_1499 c row,
    constraint_1500 c row,
    constraint_1501 c row
  ]

-- APrime group 1 block 4 booleans (64 items)
def seg_E_ap_1_bool_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1502 c row,
    constraint_1503 c row,
    constraint_1504 c row,
    constraint_1505 c row,
    constraint_1506 c row,
    constraint_1507 c row,
    constraint_1508 c row,
    constraint_1509 c row,
    constraint_1510 c row,
    constraint_1511 c row,
    constraint_1512 c row,
    constraint_1513 c row,
    constraint_1514 c row,
    constraint_1515 c row,
    constraint_1516 c row,
    constraint_1517 c row,
    constraint_1518 c row,
    constraint_1519 c row,
    constraint_1520 c row,
    constraint_1521 c row,
    constraint_1522 c row,
    constraint_1523 c row,
    constraint_1524 c row,
    constraint_1525 c row,
    constraint_1526 c row,
    constraint_1527 c row,
    constraint_1528 c row,
    constraint_1529 c row,
    constraint_1530 c row,
    constraint_1531 c row,
    constraint_1532 c row,
    constraint_1533 c row,
    constraint_1534 c row,
    constraint_1535 c row,
    constraint_1536 c row,
    constraint_1537 c row,
    constraint_1538 c row,
    constraint_1539 c row,
    constraint_1540 c row,
    constraint_1541 c row,
    constraint_1542 c row,
    constraint_1543 c row,
    constraint_1544 c row,
    constraint_1545 c row,
    constraint_1546 c row,
    constraint_1547 c row,
    constraint_1548 c row,
    constraint_1549 c row,
    constraint_1550 c row,
    constraint_1551 c row,
    constraint_1552 c row,
    constraint_1553 c row,
    constraint_1554 c row,
    constraint_1555 c row,
    constraint_1556 c row,
    constraint_1557 c row,
    constraint_1558 c row,
    constraint_1559 c row,
    constraint_1560 c row,
    constraint_1561 c row,
    constraint_1562 c row,
    constraint_1563 c row,
    constraint_1564 c row,
    constraint_1565 c row
  ]

-- APrime group 1 block 4 xor3 (4 items)
def seg_E_ap_1_xor3_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1566 c row,
    constraint_1567 c row,
    constraint_1568 c row,
    constraint_1569 c row
  ]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 65536 in
lemma seg_E_ap_1_eq_chunks
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1 c row =
      seg_E_ap_1_bool_0 c row ++
      seg_E_ap_1_xor3_0 c row ++
      seg_E_ap_1_bool_1 c row ++
      seg_E_ap_1_xor3_1 c row ++
      seg_E_ap_1_bool_2 c row ++
      seg_E_ap_1_xor3_2 c row ++
      seg_E_ap_1_bool_3 c row ++
      seg_E_ap_1_xor3_3 c row ++
      seg_E_ap_1_bool_4 c row ++
      seg_E_ap_1_xor3_4 c row := by rfl

-- APrime group 2 block 0 booleans (64 items)
def seg_E_ap_2_bool_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1570 c row,
    constraint_1571 c row,
    constraint_1572 c row,
    constraint_1573 c row,
    constraint_1574 c row,
    constraint_1575 c row,
    constraint_1576 c row,
    constraint_1577 c row,
    constraint_1578 c row,
    constraint_1579 c row,
    constraint_1580 c row,
    constraint_1581 c row,
    constraint_1582 c row,
    constraint_1583 c row,
    constraint_1584 c row,
    constraint_1585 c row,
    constraint_1586 c row,
    constraint_1587 c row,
    constraint_1588 c row,
    constraint_1589 c row,
    constraint_1590 c row,
    constraint_1591 c row,
    constraint_1592 c row,
    constraint_1593 c row,
    constraint_1594 c row,
    constraint_1595 c row,
    constraint_1596 c row,
    constraint_1597 c row,
    constraint_1598 c row,
    constraint_1599 c row,
    constraint_1600 c row,
    constraint_1601 c row,
    constraint_1602 c row,
    constraint_1603 c row,
    constraint_1604 c row,
    constraint_1605 c row,
    constraint_1606 c row,
    constraint_1607 c row,
    constraint_1608 c row,
    constraint_1609 c row,
    constraint_1610 c row,
    constraint_1611 c row,
    constraint_1612 c row,
    constraint_1613 c row,
    constraint_1614 c row,
    constraint_1615 c row,
    constraint_1616 c row,
    constraint_1617 c row,
    constraint_1618 c row,
    constraint_1619 c row,
    constraint_1620 c row,
    constraint_1621 c row,
    constraint_1622 c row,
    constraint_1623 c row,
    constraint_1624 c row,
    constraint_1625 c row,
    constraint_1626 c row,
    constraint_1627 c row,
    constraint_1628 c row,
    constraint_1629 c row,
    constraint_1630 c row,
    constraint_1631 c row,
    constraint_1632 c row,
    constraint_1633 c row
  ]

-- APrime group 2 block 0 xor3 (4 items)
def seg_E_ap_2_xor3_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1634 c row,
    constraint_1635 c row,
    constraint_1636 c row,
    constraint_1637 c row
  ]

-- APrime group 2 block 1 booleans (64 items)
def seg_E_ap_2_bool_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1638 c row,
    constraint_1639 c row,
    constraint_1640 c row,
    constraint_1641 c row,
    constraint_1642 c row,
    constraint_1643 c row,
    constraint_1644 c row,
    constraint_1645 c row,
    constraint_1646 c row,
    constraint_1647 c row,
    constraint_1648 c row,
    constraint_1649 c row,
    constraint_1650 c row,
    constraint_1651 c row,
    constraint_1652 c row,
    constraint_1653 c row,
    constraint_1654 c row,
    constraint_1655 c row,
    constraint_1656 c row,
    constraint_1657 c row,
    constraint_1658 c row,
    constraint_1659 c row,
    constraint_1660 c row,
    constraint_1661 c row,
    constraint_1662 c row,
    constraint_1663 c row,
    constraint_1664 c row,
    constraint_1665 c row,
    constraint_1666 c row,
    constraint_1667 c row,
    constraint_1668 c row,
    constraint_1669 c row,
    constraint_1670 c row,
    constraint_1671 c row,
    constraint_1672 c row,
    constraint_1673 c row,
    constraint_1674 c row,
    constraint_1675 c row,
    constraint_1676 c row,
    constraint_1677 c row,
    constraint_1678 c row,
    constraint_1679 c row,
    constraint_1680 c row,
    constraint_1681 c row,
    constraint_1682 c row,
    constraint_1683 c row,
    constraint_1684 c row,
    constraint_1685 c row,
    constraint_1686 c row,
    constraint_1687 c row,
    constraint_1688 c row,
    constraint_1689 c row,
    constraint_1690 c row,
    constraint_1691 c row,
    constraint_1692 c row,
    constraint_1693 c row,
    constraint_1694 c row,
    constraint_1695 c row,
    constraint_1696 c row,
    constraint_1697 c row,
    constraint_1698 c row,
    constraint_1699 c row,
    constraint_1700 c row,
    constraint_1701 c row
  ]

-- APrime group 2 block 1 xor3 (4 items)
def seg_E_ap_2_xor3_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1702 c row,
    constraint_1703 c row,
    constraint_1704 c row,
    constraint_1705 c row
  ]

-- APrime group 2 block 2 booleans (64 items)
def seg_E_ap_2_bool_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1706 c row,
    constraint_1707 c row,
    constraint_1708 c row,
    constraint_1709 c row,
    constraint_1710 c row,
    constraint_1711 c row,
    constraint_1712 c row,
    constraint_1713 c row,
    constraint_1714 c row,
    constraint_1715 c row,
    constraint_1716 c row,
    constraint_1717 c row,
    constraint_1718 c row,
    constraint_1719 c row,
    constraint_1720 c row,
    constraint_1721 c row,
    constraint_1722 c row,
    constraint_1723 c row,
    constraint_1724 c row,
    constraint_1725 c row,
    constraint_1726 c row,
    constraint_1727 c row,
    constraint_1728 c row,
    constraint_1729 c row,
    constraint_1730 c row,
    constraint_1731 c row,
    constraint_1732 c row,
    constraint_1733 c row,
    constraint_1734 c row,
    constraint_1735 c row,
    constraint_1736 c row,
    constraint_1737 c row,
    constraint_1738 c row,
    constraint_1739 c row,
    constraint_1740 c row,
    constraint_1741 c row,
    constraint_1742 c row,
    constraint_1743 c row,
    constraint_1744 c row,
    constraint_1745 c row,
    constraint_1746 c row,
    constraint_1747 c row,
    constraint_1748 c row,
    constraint_1749 c row,
    constraint_1750 c row,
    constraint_1751 c row,
    constraint_1752 c row,
    constraint_1753 c row,
    constraint_1754 c row,
    constraint_1755 c row,
    constraint_1756 c row,
    constraint_1757 c row,
    constraint_1758 c row,
    constraint_1759 c row,
    constraint_1760 c row,
    constraint_1761 c row,
    constraint_1762 c row,
    constraint_1763 c row,
    constraint_1764 c row,
    constraint_1765 c row,
    constraint_1766 c row,
    constraint_1767 c row,
    constraint_1768 c row,
    constraint_1769 c row
  ]

-- APrime group 2 block 2 xor3 (4 items)
def seg_E_ap_2_xor3_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1770 c row,
    constraint_1771 c row,
    constraint_1772 c row,
    constraint_1773 c row
  ]

-- APrime group 2 block 3 booleans (64 items)
def seg_E_ap_2_bool_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1774 c row,
    constraint_1775 c row,
    constraint_1776 c row,
    constraint_1777 c row,
    constraint_1778 c row,
    constraint_1779 c row,
    constraint_1780 c row,
    constraint_1781 c row,
    constraint_1782 c row,
    constraint_1783 c row,
    constraint_1784 c row,
    constraint_1785 c row,
    constraint_1786 c row,
    constraint_1787 c row,
    constraint_1788 c row,
    constraint_1789 c row,
    constraint_1790 c row,
    constraint_1791 c row,
    constraint_1792 c row,
    constraint_1793 c row,
    constraint_1794 c row,
    constraint_1795 c row,
    constraint_1796 c row,
    constraint_1797 c row,
    constraint_1798 c row,
    constraint_1799 c row,
    constraint_1800 c row,
    constraint_1801 c row,
    constraint_1802 c row,
    constraint_1803 c row,
    constraint_1804 c row,
    constraint_1805 c row,
    constraint_1806 c row,
    constraint_1807 c row,
    constraint_1808 c row,
    constraint_1809 c row,
    constraint_1810 c row,
    constraint_1811 c row,
    constraint_1812 c row,
    constraint_1813 c row,
    constraint_1814 c row,
    constraint_1815 c row,
    constraint_1816 c row,
    constraint_1817 c row,
    constraint_1818 c row,
    constraint_1819 c row,
    constraint_1820 c row,
    constraint_1821 c row,
    constraint_1822 c row,
    constraint_1823 c row,
    constraint_1824 c row,
    constraint_1825 c row,
    constraint_1826 c row,
    constraint_1827 c row,
    constraint_1828 c row,
    constraint_1829 c row,
    constraint_1830 c row,
    constraint_1831 c row,
    constraint_1832 c row,
    constraint_1833 c row,
    constraint_1834 c row,
    constraint_1835 c row,
    constraint_1836 c row,
    constraint_1837 c row
  ]

-- APrime group 2 block 3 xor3 (4 items)
def seg_E_ap_2_xor3_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1838 c row,
    constraint_1839 c row,
    constraint_1840 c row,
    constraint_1841 c row
  ]

-- APrime group 2 block 4 booleans (64 items)
def seg_E_ap_2_bool_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1842 c row,
    constraint_1843 c row,
    constraint_1844 c row,
    constraint_1845 c row,
    constraint_1846 c row,
    constraint_1847 c row,
    constraint_1848 c row,
    constraint_1849 c row,
    constraint_1850 c row,
    constraint_1851 c row,
    constraint_1852 c row,
    constraint_1853 c row,
    constraint_1854 c row,
    constraint_1855 c row,
    constraint_1856 c row,
    constraint_1857 c row,
    constraint_1858 c row,
    constraint_1859 c row,
    constraint_1860 c row,
    constraint_1861 c row,
    constraint_1862 c row,
    constraint_1863 c row,
    constraint_1864 c row,
    constraint_1865 c row,
    constraint_1866 c row,
    constraint_1867 c row,
    constraint_1868 c row,
    constraint_1869 c row,
    constraint_1870 c row,
    constraint_1871 c row,
    constraint_1872 c row,
    constraint_1873 c row,
    constraint_1874 c row,
    constraint_1875 c row,
    constraint_1876 c row,
    constraint_1877 c row,
    constraint_1878 c row,
    constraint_1879 c row,
    constraint_1880 c row,
    constraint_1881 c row,
    constraint_1882 c row,
    constraint_1883 c row,
    constraint_1884 c row,
    constraint_1885 c row,
    constraint_1886 c row,
    constraint_1887 c row,
    constraint_1888 c row,
    constraint_1889 c row,
    constraint_1890 c row,
    constraint_1891 c row,
    constraint_1892 c row,
    constraint_1893 c row,
    constraint_1894 c row,
    constraint_1895 c row,
    constraint_1896 c row,
    constraint_1897 c row,
    constraint_1898 c row,
    constraint_1899 c row,
    constraint_1900 c row,
    constraint_1901 c row,
    constraint_1902 c row,
    constraint_1903 c row,
    constraint_1904 c row,
    constraint_1905 c row
  ]

-- APrime group 2 block 4 xor3 (4 items)
def seg_E_ap_2_xor3_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1906 c row,
    constraint_1907 c row,
    constraint_1908 c row,
    constraint_1909 c row
  ]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 65536 in
lemma seg_E_ap_2_eq_chunks
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2 c row =
      seg_E_ap_2_bool_0 c row ++
      seg_E_ap_2_xor3_0 c row ++
      seg_E_ap_2_bool_1 c row ++
      seg_E_ap_2_xor3_1 c row ++
      seg_E_ap_2_bool_2 c row ++
      seg_E_ap_2_xor3_2 c row ++
      seg_E_ap_2_bool_3 c row ++
      seg_E_ap_2_xor3_3 c row ++
      seg_E_ap_2_bool_4 c row ++
      seg_E_ap_2_xor3_4 c row := by rfl

-- APrime group 3 block 0 booleans (64 items)
def seg_E_ap_3_bool_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1910 c row,
    constraint_1911 c row,
    constraint_1912 c row,
    constraint_1913 c row,
    constraint_1914 c row,
    constraint_1915 c row,
    constraint_1916 c row,
    constraint_1917 c row,
    constraint_1918 c row,
    constraint_1919 c row,
    constraint_1920 c row,
    constraint_1921 c row,
    constraint_1922 c row,
    constraint_1923 c row,
    constraint_1924 c row,
    constraint_1925 c row,
    constraint_1926 c row,
    constraint_1927 c row,
    constraint_1928 c row,
    constraint_1929 c row,
    constraint_1930 c row,
    constraint_1931 c row,
    constraint_1932 c row,
    constraint_1933 c row,
    constraint_1934 c row,
    constraint_1935 c row,
    constraint_1936 c row,
    constraint_1937 c row,
    constraint_1938 c row,
    constraint_1939 c row,
    constraint_1940 c row,
    constraint_1941 c row,
    constraint_1942 c row,
    constraint_1943 c row,
    constraint_1944 c row,
    constraint_1945 c row,
    constraint_1946 c row,
    constraint_1947 c row,
    constraint_1948 c row,
    constraint_1949 c row,
    constraint_1950 c row,
    constraint_1951 c row,
    constraint_1952 c row,
    constraint_1953 c row,
    constraint_1954 c row,
    constraint_1955 c row,
    constraint_1956 c row,
    constraint_1957 c row,
    constraint_1958 c row,
    constraint_1959 c row,
    constraint_1960 c row,
    constraint_1961 c row,
    constraint_1962 c row,
    constraint_1963 c row,
    constraint_1964 c row,
    constraint_1965 c row,
    constraint_1966 c row,
    constraint_1967 c row,
    constraint_1968 c row,
    constraint_1969 c row,
    constraint_1970 c row,
    constraint_1971 c row,
    constraint_1972 c row,
    constraint_1973 c row
  ]

-- APrime group 3 block 0 xor3 (4 items)
def seg_E_ap_3_xor3_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1974 c row,
    constraint_1975 c row,
    constraint_1976 c row,
    constraint_1977 c row
  ]

-- APrime group 3 block 1 booleans (64 items)
def seg_E_ap_3_bool_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_1978 c row,
    constraint_1979 c row,
    constraint_1980 c row,
    constraint_1981 c row,
    constraint_1982 c row,
    constraint_1983 c row,
    constraint_1984 c row,
    constraint_1985 c row,
    constraint_1986 c row,
    constraint_1987 c row,
    constraint_1988 c row,
    constraint_1989 c row,
    constraint_1990 c row,
    constraint_1991 c row,
    constraint_1992 c row,
    constraint_1993 c row,
    constraint_1994 c row,
    constraint_1995 c row,
    constraint_1996 c row,
    constraint_1997 c row,
    constraint_1998 c row,
    constraint_1999 c row,
    constraint_2000 c row,
    constraint_2001 c row,
    constraint_2002 c row,
    constraint_2003 c row,
    constraint_2004 c row,
    constraint_2005 c row,
    constraint_2006 c row,
    constraint_2007 c row,
    constraint_2008 c row,
    constraint_2009 c row,
    constraint_2010 c row,
    constraint_2011 c row,
    constraint_2012 c row,
    constraint_2013 c row,
    constraint_2014 c row,
    constraint_2015 c row,
    constraint_2016 c row,
    constraint_2017 c row,
    constraint_2018 c row,
    constraint_2019 c row,
    constraint_2020 c row,
    constraint_2021 c row,
    constraint_2022 c row,
    constraint_2023 c row,
    constraint_2024 c row,
    constraint_2025 c row,
    constraint_2026 c row,
    constraint_2027 c row,
    constraint_2028 c row,
    constraint_2029 c row,
    constraint_2030 c row,
    constraint_2031 c row,
    constraint_2032 c row,
    constraint_2033 c row,
    constraint_2034 c row,
    constraint_2035 c row,
    constraint_2036 c row,
    constraint_2037 c row,
    constraint_2038 c row,
    constraint_2039 c row,
    constraint_2040 c row,
    constraint_2041 c row
  ]

-- APrime group 3 block 1 xor3 (4 items)
def seg_E_ap_3_xor3_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2042 c row,
    constraint_2043 c row,
    constraint_2044 c row,
    constraint_2045 c row
  ]

-- APrime group 3 block 2 booleans (64 items)
def seg_E_ap_3_bool_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2046 c row,
    constraint_2047 c row,
    constraint_2048 c row,
    constraint_2049 c row,
    constraint_2050 c row,
    constraint_2051 c row,
    constraint_2052 c row,
    constraint_2053 c row,
    constraint_2054 c row,
    constraint_2055 c row,
    constraint_2056 c row,
    constraint_2057 c row,
    constraint_2058 c row,
    constraint_2059 c row,
    constraint_2060 c row,
    constraint_2061 c row,
    constraint_2062 c row,
    constraint_2063 c row,
    constraint_2064 c row,
    constraint_2065 c row,
    constraint_2066 c row,
    constraint_2067 c row,
    constraint_2068 c row,
    constraint_2069 c row,
    constraint_2070 c row,
    constraint_2071 c row,
    constraint_2072 c row,
    constraint_2073 c row,
    constraint_2074 c row,
    constraint_2075 c row,
    constraint_2076 c row,
    constraint_2077 c row,
    constraint_2078 c row,
    constraint_2079 c row,
    constraint_2080 c row,
    constraint_2081 c row,
    constraint_2082 c row,
    constraint_2083 c row,
    constraint_2084 c row,
    constraint_2085 c row,
    constraint_2086 c row,
    constraint_2087 c row,
    constraint_2088 c row,
    constraint_2089 c row,
    constraint_2090 c row,
    constraint_2091 c row,
    constraint_2092 c row,
    constraint_2093 c row,
    constraint_2094 c row,
    constraint_2095 c row,
    constraint_2096 c row,
    constraint_2097 c row,
    constraint_2098 c row,
    constraint_2099 c row,
    constraint_2100 c row,
    constraint_2101 c row,
    constraint_2102 c row,
    constraint_2103 c row,
    constraint_2104 c row,
    constraint_2105 c row,
    constraint_2106 c row,
    constraint_2107 c row,
    constraint_2108 c row,
    constraint_2109 c row
  ]

-- APrime group 3 block 2 xor3 (4 items)
def seg_E_ap_3_xor3_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2110 c row,
    constraint_2111 c row,
    constraint_2112 c row,
    constraint_2113 c row
  ]

-- APrime group 3 block 3 booleans (64 items)
def seg_E_ap_3_bool_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2114 c row,
    constraint_2115 c row,
    constraint_2116 c row,
    constraint_2117 c row,
    constraint_2118 c row,
    constraint_2119 c row,
    constraint_2120 c row,
    constraint_2121 c row,
    constraint_2122 c row,
    constraint_2123 c row,
    constraint_2124 c row,
    constraint_2125 c row,
    constraint_2126 c row,
    constraint_2127 c row,
    constraint_2128 c row,
    constraint_2129 c row,
    constraint_2130 c row,
    constraint_2131 c row,
    constraint_2132 c row,
    constraint_2133 c row,
    constraint_2134 c row,
    constraint_2135 c row,
    constraint_2136 c row,
    constraint_2137 c row,
    constraint_2138 c row,
    constraint_2139 c row,
    constraint_2140 c row,
    constraint_2141 c row,
    constraint_2142 c row,
    constraint_2143 c row,
    constraint_2144 c row,
    constraint_2145 c row,
    constraint_2146 c row,
    constraint_2147 c row,
    constraint_2148 c row,
    constraint_2149 c row,
    constraint_2150 c row,
    constraint_2151 c row,
    constraint_2152 c row,
    constraint_2153 c row,
    constraint_2154 c row,
    constraint_2155 c row,
    constraint_2156 c row,
    constraint_2157 c row,
    constraint_2158 c row,
    constraint_2159 c row,
    constraint_2160 c row,
    constraint_2161 c row,
    constraint_2162 c row,
    constraint_2163 c row,
    constraint_2164 c row,
    constraint_2165 c row,
    constraint_2166 c row,
    constraint_2167 c row,
    constraint_2168 c row,
    constraint_2169 c row,
    constraint_2170 c row,
    constraint_2171 c row,
    constraint_2172 c row,
    constraint_2173 c row,
    constraint_2174 c row,
    constraint_2175 c row,
    constraint_2176 c row,
    constraint_2177 c row
  ]

-- APrime group 3 block 3 xor3 (4 items)
def seg_E_ap_3_xor3_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2178 c row,
    constraint_2179 c row,
    constraint_2180 c row,
    constraint_2181 c row
  ]

-- APrime group 3 block 4 booleans (64 items)
def seg_E_ap_3_bool_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2182 c row,
    constraint_2183 c row,
    constraint_2184 c row,
    constraint_2185 c row,
    constraint_2186 c row,
    constraint_2187 c row,
    constraint_2188 c row,
    constraint_2189 c row,
    constraint_2190 c row,
    constraint_2191 c row,
    constraint_2192 c row,
    constraint_2193 c row,
    constraint_2194 c row,
    constraint_2195 c row,
    constraint_2196 c row,
    constraint_2197 c row,
    constraint_2198 c row,
    constraint_2199 c row,
    constraint_2200 c row,
    constraint_2201 c row,
    constraint_2202 c row,
    constraint_2203 c row,
    constraint_2204 c row,
    constraint_2205 c row,
    constraint_2206 c row,
    constraint_2207 c row,
    constraint_2208 c row,
    constraint_2209 c row,
    constraint_2210 c row,
    constraint_2211 c row,
    constraint_2212 c row,
    constraint_2213 c row,
    constraint_2214 c row,
    constraint_2215 c row,
    constraint_2216 c row,
    constraint_2217 c row,
    constraint_2218 c row,
    constraint_2219 c row,
    constraint_2220 c row,
    constraint_2221 c row,
    constraint_2222 c row,
    constraint_2223 c row,
    constraint_2224 c row,
    constraint_2225 c row,
    constraint_2226 c row,
    constraint_2227 c row,
    constraint_2228 c row,
    constraint_2229 c row,
    constraint_2230 c row,
    constraint_2231 c row,
    constraint_2232 c row,
    constraint_2233 c row,
    constraint_2234 c row,
    constraint_2235 c row,
    constraint_2236 c row,
    constraint_2237 c row,
    constraint_2238 c row,
    constraint_2239 c row,
    constraint_2240 c row,
    constraint_2241 c row,
    constraint_2242 c row,
    constraint_2243 c row,
    constraint_2244 c row,
    constraint_2245 c row
  ]

-- APrime group 3 block 4 xor3 (4 items)
def seg_E_ap_3_xor3_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2246 c row,
    constraint_2247 c row,
    constraint_2248 c row,
    constraint_2249 c row
  ]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 65536 in
lemma seg_E_ap_3_eq_chunks
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3 c row =
      seg_E_ap_3_bool_0 c row ++
      seg_E_ap_3_xor3_0 c row ++
      seg_E_ap_3_bool_1 c row ++
      seg_E_ap_3_xor3_1 c row ++
      seg_E_ap_3_bool_2 c row ++
      seg_E_ap_3_xor3_2 c row ++
      seg_E_ap_3_bool_3 c row ++
      seg_E_ap_3_xor3_3 c row ++
      seg_E_ap_3_bool_4 c row ++
      seg_E_ap_3_xor3_4 c row := by rfl

-- APrime group 4 block 0 booleans (64 items)
def seg_E_ap_4_bool_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2250 c row,
    constraint_2251 c row,
    constraint_2252 c row,
    constraint_2253 c row,
    constraint_2254 c row,
    constraint_2255 c row,
    constraint_2256 c row,
    constraint_2257 c row,
    constraint_2258 c row,
    constraint_2259 c row,
    constraint_2260 c row,
    constraint_2261 c row,
    constraint_2262 c row,
    constraint_2263 c row,
    constraint_2264 c row,
    constraint_2265 c row,
    constraint_2266 c row,
    constraint_2267 c row,
    constraint_2268 c row,
    constraint_2269 c row,
    constraint_2270 c row,
    constraint_2271 c row,
    constraint_2272 c row,
    constraint_2273 c row,
    constraint_2274 c row,
    constraint_2275 c row,
    constraint_2276 c row,
    constraint_2277 c row,
    constraint_2278 c row,
    constraint_2279 c row,
    constraint_2280 c row,
    constraint_2281 c row,
    constraint_2282 c row,
    constraint_2283 c row,
    constraint_2284 c row,
    constraint_2285 c row,
    constraint_2286 c row,
    constraint_2287 c row,
    constraint_2288 c row,
    constraint_2289 c row,
    constraint_2290 c row,
    constraint_2291 c row,
    constraint_2292 c row,
    constraint_2293 c row,
    constraint_2294 c row,
    constraint_2295 c row,
    constraint_2296 c row,
    constraint_2297 c row,
    constraint_2298 c row,
    constraint_2299 c row,
    constraint_2300 c row,
    constraint_2301 c row,
    constraint_2302 c row,
    constraint_2303 c row,
    constraint_2304 c row,
    constraint_2305 c row,
    constraint_2306 c row,
    constraint_2307 c row,
    constraint_2308 c row,
    constraint_2309 c row,
    constraint_2310 c row,
    constraint_2311 c row,
    constraint_2312 c row,
    constraint_2313 c row
  ]

-- APrime group 4 block 0 xor3 (4 items)
def seg_E_ap_4_xor3_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2314 c row,
    constraint_2315 c row,
    constraint_2316 c row,
    constraint_2317 c row
  ]

-- APrime group 4 block 1 booleans (64 items)
def seg_E_ap_4_bool_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2318 c row,
    constraint_2319 c row,
    constraint_2320 c row,
    constraint_2321 c row,
    constraint_2322 c row,
    constraint_2323 c row,
    constraint_2324 c row,
    constraint_2325 c row,
    constraint_2326 c row,
    constraint_2327 c row,
    constraint_2328 c row,
    constraint_2329 c row,
    constraint_2330 c row,
    constraint_2331 c row,
    constraint_2332 c row,
    constraint_2333 c row,
    constraint_2334 c row,
    constraint_2335 c row,
    constraint_2336 c row,
    constraint_2337 c row,
    constraint_2338 c row,
    constraint_2339 c row,
    constraint_2340 c row,
    constraint_2341 c row,
    constraint_2342 c row,
    constraint_2343 c row,
    constraint_2344 c row,
    constraint_2345 c row,
    constraint_2346 c row,
    constraint_2347 c row,
    constraint_2348 c row,
    constraint_2349 c row,
    constraint_2350 c row,
    constraint_2351 c row,
    constraint_2352 c row,
    constraint_2353 c row,
    constraint_2354 c row,
    constraint_2355 c row,
    constraint_2356 c row,
    constraint_2357 c row,
    constraint_2358 c row,
    constraint_2359 c row,
    constraint_2360 c row,
    constraint_2361 c row,
    constraint_2362 c row,
    constraint_2363 c row,
    constraint_2364 c row,
    constraint_2365 c row,
    constraint_2366 c row,
    constraint_2367 c row,
    constraint_2368 c row,
    constraint_2369 c row,
    constraint_2370 c row,
    constraint_2371 c row,
    constraint_2372 c row,
    constraint_2373 c row,
    constraint_2374 c row,
    constraint_2375 c row,
    constraint_2376 c row,
    constraint_2377 c row,
    constraint_2378 c row,
    constraint_2379 c row,
    constraint_2380 c row,
    constraint_2381 c row
  ]

-- APrime group 4 block 1 xor3 (4 items)
def seg_E_ap_4_xor3_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2382 c row,
    constraint_2383 c row,
    constraint_2384 c row,
    constraint_2385 c row
  ]

-- APrime group 4 block 2 booleans (64 items)
def seg_E_ap_4_bool_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2386 c row,
    constraint_2387 c row,
    constraint_2388 c row,
    constraint_2389 c row,
    constraint_2390 c row,
    constraint_2391 c row,
    constraint_2392 c row,
    constraint_2393 c row,
    constraint_2394 c row,
    constraint_2395 c row,
    constraint_2396 c row,
    constraint_2397 c row,
    constraint_2398 c row,
    constraint_2399 c row,
    constraint_2400 c row,
    constraint_2401 c row,
    constraint_2402 c row,
    constraint_2403 c row,
    constraint_2404 c row,
    constraint_2405 c row,
    constraint_2406 c row,
    constraint_2407 c row,
    constraint_2408 c row,
    constraint_2409 c row,
    constraint_2410 c row,
    constraint_2411 c row,
    constraint_2412 c row,
    constraint_2413 c row,
    constraint_2414 c row,
    constraint_2415 c row,
    constraint_2416 c row,
    constraint_2417 c row,
    constraint_2418 c row,
    constraint_2419 c row,
    constraint_2420 c row,
    constraint_2421 c row,
    constraint_2422 c row,
    constraint_2423 c row,
    constraint_2424 c row,
    constraint_2425 c row,
    constraint_2426 c row,
    constraint_2427 c row,
    constraint_2428 c row,
    constraint_2429 c row,
    constraint_2430 c row,
    constraint_2431 c row,
    constraint_2432 c row,
    constraint_2433 c row,
    constraint_2434 c row,
    constraint_2435 c row,
    constraint_2436 c row,
    constraint_2437 c row,
    constraint_2438 c row,
    constraint_2439 c row,
    constraint_2440 c row,
    constraint_2441 c row,
    constraint_2442 c row,
    constraint_2443 c row,
    constraint_2444 c row,
    constraint_2445 c row,
    constraint_2446 c row,
    constraint_2447 c row,
    constraint_2448 c row,
    constraint_2449 c row
  ]

-- APrime group 4 block 2 xor3 (4 items)
def seg_E_ap_4_xor3_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2450 c row,
    constraint_2451 c row,
    constraint_2452 c row,
    constraint_2453 c row
  ]

-- APrime group 4 block 3 booleans (64 items)
def seg_E_ap_4_bool_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2454 c row,
    constraint_2455 c row,
    constraint_2456 c row,
    constraint_2457 c row,
    constraint_2458 c row,
    constraint_2459 c row,
    constraint_2460 c row,
    constraint_2461 c row,
    constraint_2462 c row,
    constraint_2463 c row,
    constraint_2464 c row,
    constraint_2465 c row,
    constraint_2466 c row,
    constraint_2467 c row,
    constraint_2468 c row,
    constraint_2469 c row,
    constraint_2470 c row,
    constraint_2471 c row,
    constraint_2472 c row,
    constraint_2473 c row,
    constraint_2474 c row,
    constraint_2475 c row,
    constraint_2476 c row,
    constraint_2477 c row,
    constraint_2478 c row,
    constraint_2479 c row,
    constraint_2480 c row,
    constraint_2481 c row,
    constraint_2482 c row,
    constraint_2483 c row,
    constraint_2484 c row,
    constraint_2485 c row,
    constraint_2486 c row,
    constraint_2487 c row,
    constraint_2488 c row,
    constraint_2489 c row,
    constraint_2490 c row,
    constraint_2491 c row,
    constraint_2492 c row,
    constraint_2493 c row,
    constraint_2494 c row,
    constraint_2495 c row,
    constraint_2496 c row,
    constraint_2497 c row,
    constraint_2498 c row,
    constraint_2499 c row,
    constraint_2500 c row,
    constraint_2501 c row,
    constraint_2502 c row,
    constraint_2503 c row,
    constraint_2504 c row,
    constraint_2505 c row,
    constraint_2506 c row,
    constraint_2507 c row,
    constraint_2508 c row,
    constraint_2509 c row,
    constraint_2510 c row,
    constraint_2511 c row,
    constraint_2512 c row,
    constraint_2513 c row,
    constraint_2514 c row,
    constraint_2515 c row,
    constraint_2516 c row,
    constraint_2517 c row
  ]

-- APrime group 4 block 3 xor3 (4 items)
def seg_E_ap_4_xor3_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2518 c row,
    constraint_2519 c row,
    constraint_2520 c row,
    constraint_2521 c row
  ]

-- APrime group 4 block 4 booleans (64 items)
def seg_E_ap_4_bool_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2522 c row,
    constraint_2523 c row,
    constraint_2524 c row,
    constraint_2525 c row,
    constraint_2526 c row,
    constraint_2527 c row,
    constraint_2528 c row,
    constraint_2529 c row,
    constraint_2530 c row,
    constraint_2531 c row,
    constraint_2532 c row,
    constraint_2533 c row,
    constraint_2534 c row,
    constraint_2535 c row,
    constraint_2536 c row,
    constraint_2537 c row,
    constraint_2538 c row,
    constraint_2539 c row,
    constraint_2540 c row,
    constraint_2541 c row,
    constraint_2542 c row,
    constraint_2543 c row,
    constraint_2544 c row,
    constraint_2545 c row,
    constraint_2546 c row,
    constraint_2547 c row,
    constraint_2548 c row,
    constraint_2549 c row,
    constraint_2550 c row,
    constraint_2551 c row,
    constraint_2552 c row,
    constraint_2553 c row,
    constraint_2554 c row,
    constraint_2555 c row,
    constraint_2556 c row,
    constraint_2557 c row,
    constraint_2558 c row,
    constraint_2559 c row,
    constraint_2560 c row,
    constraint_2561 c row,
    constraint_2562 c row,
    constraint_2563 c row,
    constraint_2564 c row,
    constraint_2565 c row,
    constraint_2566 c row,
    constraint_2567 c row,
    constraint_2568 c row,
    constraint_2569 c row,
    constraint_2570 c row,
    constraint_2571 c row,
    constraint_2572 c row,
    constraint_2573 c row,
    constraint_2574 c row,
    constraint_2575 c row,
    constraint_2576 c row,
    constraint_2577 c row,
    constraint_2578 c row,
    constraint_2579 c row,
    constraint_2580 c row,
    constraint_2581 c row,
    constraint_2582 c row,
    constraint_2583 c row,
    constraint_2584 c row,
    constraint_2585 c row
  ]

-- APrime group 4 block 4 xor3 (4 items)
def seg_E_ap_4_xor3_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2586 c row,
    constraint_2587 c row,
    constraint_2588 c row,
    constraint_2589 c row
  ]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 65536 in
lemma seg_E_ap_4_eq_chunks
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4 c row =
      seg_E_ap_4_bool_0 c row ++
      seg_E_ap_4_xor3_0 c row ++
      seg_E_ap_4_bool_1 c row ++
      seg_E_ap_4_xor3_1 c row ++
      seg_E_ap_4_bool_2 c row ++
      seg_E_ap_4_xor3_2 c row ++
      seg_E_ap_4_bool_3 c row ++
      seg_E_ap_4_xor3_3 c row ++
      seg_E_ap_4_bool_4 c row ++
      seg_E_ap_4_xor3_4 c row := by rfl

-- Parity chunk 0 (64 items, constraints 2590-2653)
def seg_E_parity_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2590 c row,
    constraint_2591 c row,
    constraint_2592 c row,
    constraint_2593 c row,
    constraint_2594 c row,
    constraint_2595 c row,
    constraint_2596 c row,
    constraint_2597 c row,
    constraint_2598 c row,
    constraint_2599 c row,
    constraint_2600 c row,
    constraint_2601 c row,
    constraint_2602 c row,
    constraint_2603 c row,
    constraint_2604 c row,
    constraint_2605 c row,
    constraint_2606 c row,
    constraint_2607 c row,
    constraint_2608 c row,
    constraint_2609 c row,
    constraint_2610 c row,
    constraint_2611 c row,
    constraint_2612 c row,
    constraint_2613 c row,
    constraint_2614 c row,
    constraint_2615 c row,
    constraint_2616 c row,
    constraint_2617 c row,
    constraint_2618 c row,
    constraint_2619 c row,
    constraint_2620 c row,
    constraint_2621 c row,
    constraint_2622 c row,
    constraint_2623 c row,
    constraint_2624 c row,
    constraint_2625 c row,
    constraint_2626 c row,
    constraint_2627 c row,
    constraint_2628 c row,
    constraint_2629 c row,
    constraint_2630 c row,
    constraint_2631 c row,
    constraint_2632 c row,
    constraint_2633 c row,
    constraint_2634 c row,
    constraint_2635 c row,
    constraint_2636 c row,
    constraint_2637 c row,
    constraint_2638 c row,
    constraint_2639 c row,
    constraint_2640 c row,
    constraint_2641 c row,
    constraint_2642 c row,
    constraint_2643 c row,
    constraint_2644 c row,
    constraint_2645 c row,
    constraint_2646 c row,
    constraint_2647 c row,
    constraint_2648 c row,
    constraint_2649 c row,
    constraint_2650 c row,
    constraint_2651 c row,
    constraint_2652 c row,
    constraint_2653 c row
  ]

-- Parity chunk 1 (64 items, constraints 2654-2717)
def seg_E_parity_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2654 c row,
    constraint_2655 c row,
    constraint_2656 c row,
    constraint_2657 c row,
    constraint_2658 c row,
    constraint_2659 c row,
    constraint_2660 c row,
    constraint_2661 c row,
    constraint_2662 c row,
    constraint_2663 c row,
    constraint_2664 c row,
    constraint_2665 c row,
    constraint_2666 c row,
    constraint_2667 c row,
    constraint_2668 c row,
    constraint_2669 c row,
    constraint_2670 c row,
    constraint_2671 c row,
    constraint_2672 c row,
    constraint_2673 c row,
    constraint_2674 c row,
    constraint_2675 c row,
    constraint_2676 c row,
    constraint_2677 c row,
    constraint_2678 c row,
    constraint_2679 c row,
    constraint_2680 c row,
    constraint_2681 c row,
    constraint_2682 c row,
    constraint_2683 c row,
    constraint_2684 c row,
    constraint_2685 c row,
    constraint_2686 c row,
    constraint_2687 c row,
    constraint_2688 c row,
    constraint_2689 c row,
    constraint_2690 c row,
    constraint_2691 c row,
    constraint_2692 c row,
    constraint_2693 c row,
    constraint_2694 c row,
    constraint_2695 c row,
    constraint_2696 c row,
    constraint_2697 c row,
    constraint_2698 c row,
    constraint_2699 c row,
    constraint_2700 c row,
    constraint_2701 c row,
    constraint_2702 c row,
    constraint_2703 c row,
    constraint_2704 c row,
    constraint_2705 c row,
    constraint_2706 c row,
    constraint_2707 c row,
    constraint_2708 c row,
    constraint_2709 c row,
    constraint_2710 c row,
    constraint_2711 c row,
    constraint_2712 c row,
    constraint_2713 c row,
    constraint_2714 c row,
    constraint_2715 c row,
    constraint_2716 c row,
    constraint_2717 c row
  ]

-- Parity chunk 2 (64 items, constraints 2718-2781)
def seg_E_parity_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2718 c row,
    constraint_2719 c row,
    constraint_2720 c row,
    constraint_2721 c row,
    constraint_2722 c row,
    constraint_2723 c row,
    constraint_2724 c row,
    constraint_2725 c row,
    constraint_2726 c row,
    constraint_2727 c row,
    constraint_2728 c row,
    constraint_2729 c row,
    constraint_2730 c row,
    constraint_2731 c row,
    constraint_2732 c row,
    constraint_2733 c row,
    constraint_2734 c row,
    constraint_2735 c row,
    constraint_2736 c row,
    constraint_2737 c row,
    constraint_2738 c row,
    constraint_2739 c row,
    constraint_2740 c row,
    constraint_2741 c row,
    constraint_2742 c row,
    constraint_2743 c row,
    constraint_2744 c row,
    constraint_2745 c row,
    constraint_2746 c row,
    constraint_2747 c row,
    constraint_2748 c row,
    constraint_2749 c row,
    constraint_2750 c row,
    constraint_2751 c row,
    constraint_2752 c row,
    constraint_2753 c row,
    constraint_2754 c row,
    constraint_2755 c row,
    constraint_2756 c row,
    constraint_2757 c row,
    constraint_2758 c row,
    constraint_2759 c row,
    constraint_2760 c row,
    constraint_2761 c row,
    constraint_2762 c row,
    constraint_2763 c row,
    constraint_2764 c row,
    constraint_2765 c row,
    constraint_2766 c row,
    constraint_2767 c row,
    constraint_2768 c row,
    constraint_2769 c row,
    constraint_2770 c row,
    constraint_2771 c row,
    constraint_2772 c row,
    constraint_2773 c row,
    constraint_2774 c row,
    constraint_2775 c row,
    constraint_2776 c row,
    constraint_2777 c row,
    constraint_2778 c row,
    constraint_2779 c row,
    constraint_2780 c row,
    constraint_2781 c row
  ]

-- Parity chunk 3 (64 items, constraints 2782-2845)
def seg_E_parity_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2782 c row,
    constraint_2783 c row,
    constraint_2784 c row,
    constraint_2785 c row,
    constraint_2786 c row,
    constraint_2787 c row,
    constraint_2788 c row,
    constraint_2789 c row,
    constraint_2790 c row,
    constraint_2791 c row,
    constraint_2792 c row,
    constraint_2793 c row,
    constraint_2794 c row,
    constraint_2795 c row,
    constraint_2796 c row,
    constraint_2797 c row,
    constraint_2798 c row,
    constraint_2799 c row,
    constraint_2800 c row,
    constraint_2801 c row,
    constraint_2802 c row,
    constraint_2803 c row,
    constraint_2804 c row,
    constraint_2805 c row,
    constraint_2806 c row,
    constraint_2807 c row,
    constraint_2808 c row,
    constraint_2809 c row,
    constraint_2810 c row,
    constraint_2811 c row,
    constraint_2812 c row,
    constraint_2813 c row,
    constraint_2814 c row,
    constraint_2815 c row,
    constraint_2816 c row,
    constraint_2817 c row,
    constraint_2818 c row,
    constraint_2819 c row,
    constraint_2820 c row,
    constraint_2821 c row,
    constraint_2822 c row,
    constraint_2823 c row,
    constraint_2824 c row,
    constraint_2825 c row,
    constraint_2826 c row,
    constraint_2827 c row,
    constraint_2828 c row,
    constraint_2829 c row,
    constraint_2830 c row,
    constraint_2831 c row,
    constraint_2832 c row,
    constraint_2833 c row,
    constraint_2834 c row,
    constraint_2835 c row,
    constraint_2836 c row,
    constraint_2837 c row,
    constraint_2838 c row,
    constraint_2839 c row,
    constraint_2840 c row,
    constraint_2841 c row,
    constraint_2842 c row,
    constraint_2843 c row,
    constraint_2844 c row,
    constraint_2845 c row
  ]

-- Parity chunk 4 (64 items, constraints 2846-2909)
def seg_E_parity_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) : List Prop :=
  [
    constraint_2846 c row,
    constraint_2847 c row,
    constraint_2848 c row,
    constraint_2849 c row,
    constraint_2850 c row,
    constraint_2851 c row,
    constraint_2852 c row,
    constraint_2853 c row,
    constraint_2854 c row,
    constraint_2855 c row,
    constraint_2856 c row,
    constraint_2857 c row,
    constraint_2858 c row,
    constraint_2859 c row,
    constraint_2860 c row,
    constraint_2861 c row,
    constraint_2862 c row,
    constraint_2863 c row,
    constraint_2864 c row,
    constraint_2865 c row,
    constraint_2866 c row,
    constraint_2867 c row,
    constraint_2868 c row,
    constraint_2869 c row,
    constraint_2870 c row,
    constraint_2871 c row,
    constraint_2872 c row,
    constraint_2873 c row,
    constraint_2874 c row,
    constraint_2875 c row,
    constraint_2876 c row,
    constraint_2877 c row,
    constraint_2878 c row,
    constraint_2879 c row,
    constraint_2880 c row,
    constraint_2881 c row,
    constraint_2882 c row,
    constraint_2883 c row,
    constraint_2884 c row,
    constraint_2885 c row,
    constraint_2886 c row,
    constraint_2887 c row,
    constraint_2888 c row,
    constraint_2889 c row,
    constraint_2890 c row,
    constraint_2891 c row,
    constraint_2892 c row,
    constraint_2893 c row,
    constraint_2894 c row,
    constraint_2895 c row,
    constraint_2896 c row,
    constraint_2897 c row,
    constraint_2898 c row,
    constraint_2899 c row,
    constraint_2900 c row,
    constraint_2901 c row,
    constraint_2902 c row,
    constraint_2903 c row,
    constraint_2904 c row,
    constraint_2905 c row,
    constraint_2906 c row,
    constraint_2907 c row,
    constraint_2908 c row,
    constraint_2909 c row
  ]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 65536 in
lemma seg_E_parity_eq_chunks
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_parity c row =
      seg_E_parity_0 c row ++
      seg_E_parity_1 c row ++
      seg_E_parity_2 c row ++
      seg_E_parity_3 c row ++
      seg_E_parity_4 c row := by rfl

lemma seg_E_cbits_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_cbits_0 c row = (List.range 64).map (fun i =>
      c_bit c (0 + i) row * (c_bit c (0 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_cbits_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_cbits_2 c row = (List.range 64).map (fun i =>
      c_bit c (64 + i) row * (c_bit c (64 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_cbits_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_cbits_4 c row = (List.range 64).map (fun i =>
      c_bit c (128 + i) row * (c_bit c (128 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_cprime_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_cprime_1 c row = (List.range 64).map (fun i =>
      c_bit c (192 + i) row * (c_bit c (192 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_cprime_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_cprime_3 c row = (List.range 64).map (fun i =>
      c_bit c (256 + i) row * (c_bit c (256 + i) row - 1) = 0) := by rfl

lemma seg_E_ap_0_bool_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0_bool_0 c row = (List.range 64).map (fun i =>
      a_prime_bit c (0 + i) row * (a_prime_bit c (0 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_0_xor3_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0_xor3_0 c row = (List.range 4).map (fun i =>
      let j := 0 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_0_bool_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0_bool_1 c row = (List.range 64).map (fun i =>
      a_prime_bit c (64 + i) row * (a_prime_bit c (64 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_0_xor3_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0_xor3_1 c row = (List.range 4).map (fun i =>
      let j := 4 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_0_bool_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0_bool_2 c row = (List.range 64).map (fun i =>
      a_prime_bit c (128 + i) row * (a_prime_bit c (128 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_0_xor3_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0_xor3_2 c row = (List.range 4).map (fun i =>
      let j := 8 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_0_bool_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0_bool_3 c row = (List.range 64).map (fun i =>
      a_prime_bit c (192 + i) row * (a_prime_bit c (192 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_0_xor3_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0_xor3_3 c row = (List.range 4).map (fun i =>
      let j := 12 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_0_bool_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0_bool_4 c row = (List.range 64).map (fun i =>
      a_prime_bit c (256 + i) row * (a_prime_bit c (256 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_0_xor3_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_0_xor3_4 c row = (List.range 4).map (fun i =>
      let j := 16 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_1_bool_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1_bool_0 c row = (List.range 64).map (fun i =>
      a_prime_bit c (320 + i) row * (a_prime_bit c (320 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_1_xor3_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1_xor3_0 c row = (List.range 4).map (fun i =>
      let j := 20 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_1_bool_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1_bool_1 c row = (List.range 64).map (fun i =>
      a_prime_bit c (384 + i) row * (a_prime_bit c (384 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_1_xor3_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1_xor3_1 c row = (List.range 4).map (fun i =>
      let j := 24 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_1_bool_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1_bool_2 c row = (List.range 64).map (fun i =>
      a_prime_bit c (448 + i) row * (a_prime_bit c (448 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_1_xor3_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1_xor3_2 c row = (List.range 4).map (fun i =>
      let j := 28 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_1_bool_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1_bool_3 c row = (List.range 64).map (fun i =>
      a_prime_bit c (512 + i) row * (a_prime_bit c (512 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_1_xor3_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1_xor3_3 c row = (List.range 4).map (fun i =>
      let j := 32 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_1_bool_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1_bool_4 c row = (List.range 64).map (fun i =>
      a_prime_bit c (576 + i) row * (a_prime_bit c (576 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_1_xor3_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_1_xor3_4 c row = (List.range 4).map (fun i =>
      let j := 36 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_2_bool_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2_bool_0 c row = (List.range 64).map (fun i =>
      a_prime_bit c (640 + i) row * (a_prime_bit c (640 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_2_xor3_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2_xor3_0 c row = (List.range 4).map (fun i =>
      let j := 40 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_2_bool_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2_bool_1 c row = (List.range 64).map (fun i =>
      a_prime_bit c (704 + i) row * (a_prime_bit c (704 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_2_xor3_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2_xor3_1 c row = (List.range 4).map (fun i =>
      let j := 44 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_2_bool_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2_bool_2 c row = (List.range 64).map (fun i =>
      a_prime_bit c (768 + i) row * (a_prime_bit c (768 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_2_xor3_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2_xor3_2 c row = (List.range 4).map (fun i =>
      let j := 48 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_2_bool_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2_bool_3 c row = (List.range 64).map (fun i =>
      a_prime_bit c (832 + i) row * (a_prime_bit c (832 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_2_xor3_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2_xor3_3 c row = (List.range 4).map (fun i =>
      let j := 52 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_2_bool_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2_bool_4 c row = (List.range 64).map (fun i =>
      a_prime_bit c (896 + i) row * (a_prime_bit c (896 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_2_xor3_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_2_xor3_4 c row = (List.range 4).map (fun i =>
      let j := 56 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_3_bool_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3_bool_0 c row = (List.range 64).map (fun i =>
      a_prime_bit c (960 + i) row * (a_prime_bit c (960 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_3_xor3_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3_xor3_0 c row = (List.range 4).map (fun i =>
      let j := 60 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_3_bool_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3_bool_1 c row = (List.range 64).map (fun i =>
      a_prime_bit c (1024 + i) row * (a_prime_bit c (1024 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_3_xor3_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3_xor3_1 c row = (List.range 4).map (fun i =>
      let j := 64 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_3_bool_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3_bool_2 c row = (List.range 64).map (fun i =>
      a_prime_bit c (1088 + i) row * (a_prime_bit c (1088 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_3_xor3_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3_xor3_2 c row = (List.range 4).map (fun i =>
      let j := 68 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_3_bool_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3_bool_3 c row = (List.range 64).map (fun i =>
      a_prime_bit c (1152 + i) row * (a_prime_bit c (1152 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_3_xor3_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3_xor3_3 c row = (List.range 4).map (fun i =>
      let j := 72 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_3_bool_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3_bool_4 c row = (List.range 64).map (fun i =>
      a_prime_bit c (1216 + i) row * (a_prime_bit c (1216 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_3_xor3_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_3_xor3_4 c row = (List.range 4).map (fun i =>
      let j := 76 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_4_bool_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4_bool_0 c row = (List.range 64).map (fun i =>
      a_prime_bit c (1280 + i) row * (a_prime_bit c (1280 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_4_xor3_0_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4_xor3_0 c row = (List.range 4).map (fun i =>
      let j := 80 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_4_bool_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4_bool_1 c row = (List.range 64).map (fun i =>
      a_prime_bit c (1344 + i) row * (a_prime_bit c (1344 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_4_xor3_1_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4_xor3_1 c row = (List.range 4).map (fun i =>
      let j := 84 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_4_bool_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4_bool_2 c row = (List.range 64).map (fun i =>
      a_prime_bit c (1408 + i) row * (a_prime_bit c (1408 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_4_xor3_2_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4_xor3_2 c row = (List.range 4).map (fun i =>
      let j := 88 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_4_bool_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4_bool_3 c row = (List.range 64).map (fun i =>
      a_prime_bit c (1472 + i) row * (a_prime_bit c (1472 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_4_xor3_3_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4_xor3_3 c row = (List.range 4).map (fun i =>
      let j := 92 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_4_bool_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4_bool_4 c row = (List.range 64).map (fun i =>
      a_prime_bit c (1536 + i) row * (a_prime_bit c (1536 + i) row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_ap_4_xor3_4_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_ap_4_xor3_4 c row = (List.range 4).map (fun i =>
      let j := 96 + i
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb)
        (545 + 64 * x + 16 * limb)
        (865 + 16 * j)
        (125 + j)
        row) := by rfl

lemma seg_E_iota_bits_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_iota_bits c row = (List.range 64).map (fun i =>
      a_pp_00_bit c i row * (a_pp_00_bit c i row - 1) = 0) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_iota_recomp_eq_map
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ) :
    seg_E_iota_recomp c row = (List.range 4).map (fun k =>
      KeccakfPermAir.extraction.recompose16_eq c (2565 + 16 * k) (2465 + k) row) := by rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_cbits_1_eq_extract
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_cbits_1 c row)) (j : ℕ) (hj : j < 64) :
    let idx := 0 + j
    let x := idx / 64
    let z := idx % 64
    let left_idx := 64 * ((x + 4) % 5) + z
    let right_shift_idx := 64 * ((x + 1) % 5) + (z + 63) % 64
    (c_prime_bit c idx row) -
      fieldXor (fieldXor (c_bit c idx row) (c_bit c left_idx row))
               (c_bit c right_shift_idx row) = 0 := by
  simp only [seg_E_cbits_1, List.forall_cons, id_eq] at h
  interval_cases j
  · have hc := h.1; simp only [constraint_314, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.1; simp only [constraint_315, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.1; simp only [constraint_316, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.1; simp only [constraint_317, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.1; simp only [constraint_318, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.1; simp only [constraint_319, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.1; simp only [constraint_320, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.1; simp only [constraint_321, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.1; simp only [constraint_322, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.1; simp only [constraint_323, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_324, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_325, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_326, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_327, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_328, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_329, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_330, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_331, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_332, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_333, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_334, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_335, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_336, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_337, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_338, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_339, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_340, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_341, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_342, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_343, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_344, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_345, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_346, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_347, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_348, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_349, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_350, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_351, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_352, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_353, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_354, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_355, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_356, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_357, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_358, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_359, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_360, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_361, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_362, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_363, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_364, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_365, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_366, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_367, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_368, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_369, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_370, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_371, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_372, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_373, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_374, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_375, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_376, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_377, fieldXor] at hc ⊢; linear_combination hc

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_cbits_3_eq_extract
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_cbits_3 c row)) (j : ℕ) (hj : j < 64) :
    let idx := 64 + j
    let x := idx / 64
    let z := idx % 64
    let left_idx := 64 * ((x + 4) % 5) + z
    let right_shift_idx := 64 * ((x + 1) % 5) + (z + 63) % 64
    (c_prime_bit c idx row) -
      fieldXor (fieldXor (c_bit c idx row) (c_bit c left_idx row))
               (c_bit c right_shift_idx row) = 0 := by
  simp only [seg_E_cbits_3, List.forall_cons, id_eq] at h
  interval_cases j
  · have hc := h.1; simp only [constraint_442, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.1; simp only [constraint_443, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.1; simp only [constraint_444, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.1; simp only [constraint_445, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.1; simp only [constraint_446, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.1; simp only [constraint_447, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.1; simp only [constraint_448, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.1; simp only [constraint_449, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.1; simp only [constraint_450, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.1; simp only [constraint_451, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_452, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_453, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_454, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_455, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_456, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_457, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_458, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_459, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_460, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_461, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_462, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_463, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_464, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_465, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_466, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_467, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_468, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_469, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_470, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_471, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_472, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_473, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_474, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_475, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_476, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_477, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_478, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_479, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_480, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_481, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_482, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_483, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_484, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_485, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_486, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_487, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_488, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_489, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_490, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_491, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_492, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_493, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_494, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_495, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_496, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_497, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_498, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_499, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_500, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_501, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_502, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_503, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_504, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_505, fieldXor] at hc ⊢; linear_combination hc

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_cprime_0_eq_extract
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_cprime_0 c row)) (j : ℕ) (hj : j < 64) :
    let idx := 128 + j
    let x := idx / 64
    let z := idx % 64
    let left_idx := 64 * ((x + 4) % 5) + z
    let right_shift_idx := 64 * ((x + 1) % 5) + (z + 63) % 64
    (c_prime_bit c idx row) -
      fieldXor (fieldXor (c_bit c idx row) (c_bit c left_idx row))
               (c_bit c right_shift_idx row) = 0 := by
  simp only [seg_E_cprime_0, List.forall_cons, id_eq] at h
  interval_cases j
  · have hc := h.1; simp only [constraint_570, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.1; simp only [constraint_571, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.1; simp only [constraint_572, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.1; simp only [constraint_573, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.1; simp only [constraint_574, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.1; simp only [constraint_575, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.1; simp only [constraint_576, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.1; simp only [constraint_577, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.1; simp only [constraint_578, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.1; simp only [constraint_579, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_580, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_581, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_582, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_583, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_584, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_585, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_586, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_587, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_588, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_589, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_590, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_591, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_592, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_593, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_594, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_595, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_596, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_597, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_598, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_599, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_600, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_601, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_602, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_603, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_604, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_605, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_606, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_607, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_608, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_609, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_610, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_611, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_612, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_613, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_614, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_615, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_616, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_617, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_618, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_619, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_620, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_621, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_622, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_623, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_624, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_625, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_626, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_627, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_628, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_629, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_630, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_631, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_632, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_633, fieldXor] at hc ⊢; linear_combination hc

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_cprime_2_eq_extract
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_cprime_2 c row)) (j : ℕ) (hj : j < 64) :
    let idx := 192 + j
    let x := idx / 64
    let z := idx % 64
    let left_idx := 64 * ((x + 4) % 5) + z
    let right_shift_idx := 64 * ((x + 1) % 5) + (z + 63) % 64
    (c_prime_bit c idx row) -
      fieldXor (fieldXor (c_bit c idx row) (c_bit c left_idx row))
               (c_bit c right_shift_idx row) = 0 := by
  simp only [seg_E_cprime_2, List.forall_cons, id_eq] at h
  interval_cases j
  · have hc := h.1; simp only [constraint_698, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.1; simp only [constraint_699, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.1; simp only [constraint_700, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.1; simp only [constraint_701, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.1; simp only [constraint_702, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.1; simp only [constraint_703, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.1; simp only [constraint_704, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.1; simp only [constraint_705, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.1; simp only [constraint_706, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.1; simp only [constraint_707, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_708, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_709, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_710, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_711, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_712, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_713, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_714, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_715, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_716, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_717, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_718, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_719, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_720, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_721, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_722, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_723, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_724, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_725, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_726, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_727, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_728, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_729, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_730, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_731, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_732, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_733, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_734, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_735, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_736, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_737, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_738, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_739, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_740, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_741, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_742, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_743, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_744, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_745, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_746, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_747, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_748, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_749, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_750, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_751, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_752, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_753, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_754, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_755, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_756, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_757, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_758, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_759, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_760, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_761, fieldXor] at hc ⊢; linear_combination hc

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_cprime_4_eq_extract
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_cprime_4 c row)) (j : ℕ) (hj : j < 64) :
    let idx := 256 + j
    let x := idx / 64
    let z := idx % 64
    let left_idx := 64 * ((x + 4) % 5) + z
    let right_shift_idx := 64 * ((x + 1) % 5) + (z + 63) % 64
    (c_prime_bit c idx row) -
      fieldXor (fieldXor (c_bit c idx row) (c_bit c left_idx row))
               (c_bit c right_shift_idx row) = 0 := by
  simp only [seg_E_cprime_4, List.forall_cons, id_eq] at h
  interval_cases j
  · have hc := h.1; simp only [constraint_826, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.1; simp only [constraint_827, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.1; simp only [constraint_828, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.1; simp only [constraint_829, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.1; simp only [constraint_830, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.1; simp only [constraint_831, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.1; simp only [constraint_832, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.1; simp only [constraint_833, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.1; simp only [constraint_834, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.1; simp only [constraint_835, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_836, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_837, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_838, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_839, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_840, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_841, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_842, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_843, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_844, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_845, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_846, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_847, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_848, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_849, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_850, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_851, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_852, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_853, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_854, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_855, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_856, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_857, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_858, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_859, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_860, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_861, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_862, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_863, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_864, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_865, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_866, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_867, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_868, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_869, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_870, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_871, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_872, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_873, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_874, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_875, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_876, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_877, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_878, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_879, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_880, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_881, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_882, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_883, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_884, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_885, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_886, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_887, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_888, fieldXor] at hc ⊢; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_889, fieldXor] at hc ⊢; linear_combination hc

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_parity_0_eq_extract
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_parity_0 c row)) (j : ℕ) (hj : j < 64) :
    let idx := 0 + j
    let sum5 := a_prime_bit c idx row + a_prime_bit c (idx + 320) row +
                a_prime_bit c (idx + 640) row + a_prime_bit c (idx + 960) row +
                a_prime_bit c (idx + 1280) row
    let diff := sum5 - c_prime_bit c idx row
    diff * (diff - 2) * (diff - 4) = 0 := by
  simp only [seg_E_parity_0, List.forall_cons, id_eq] at h
  interval_cases j
  · have hc := h.1; simp only [constraint_2590] at hc; linear_combination hc
  · have hc := h.2.1; simp only [constraint_2591] at hc; linear_combination hc
  · have hc := h.2.2.1; simp only [constraint_2592] at hc; linear_combination hc
  · have hc := h.2.2.2.1; simp only [constraint_2593] at hc; linear_combination hc
  · have hc := h.2.2.2.2.1; simp only [constraint_2594] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.1; simp only [constraint_2595] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.1; simp only [constraint_2596] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.1; simp only [constraint_2597] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.1; simp only [constraint_2598] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2599] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2600] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2601] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2602] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2603] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2604] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2605] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2606] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2607] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2608] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2609] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2610] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2611] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2612] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2613] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2614] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2615] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2616] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2617] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2618] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2619] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2620] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2621] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2622] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2623] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2624] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2625] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2626] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2627] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2628] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2629] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2630] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2631] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2632] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2633] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2634] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2635] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2636] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2637] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2638] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2639] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2640] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2641] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2642] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2643] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2644] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2645] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2646] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2647] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2648] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2649] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2650] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2651] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2652] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2653] at hc; linear_combination hc

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_parity_1_eq_extract
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_parity_1 c row)) (j : ℕ) (hj : j < 64) :
    let idx := 64 + j
    let sum5 := a_prime_bit c idx row + a_prime_bit c (idx + 320) row +
                a_prime_bit c (idx + 640) row + a_prime_bit c (idx + 960) row +
                a_prime_bit c (idx + 1280) row
    let diff := sum5 - c_prime_bit c idx row
    diff * (diff - 2) * (diff - 4) = 0 := by
  simp only [seg_E_parity_1, List.forall_cons, id_eq] at h
  interval_cases j
  · have hc := h.1; simp only [constraint_2654] at hc; linear_combination hc
  · have hc := h.2.1; simp only [constraint_2655] at hc; linear_combination hc
  · have hc := h.2.2.1; simp only [constraint_2656] at hc; linear_combination hc
  · have hc := h.2.2.2.1; simp only [constraint_2657] at hc; linear_combination hc
  · have hc := h.2.2.2.2.1; simp only [constraint_2658] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.1; simp only [constraint_2659] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.1; simp only [constraint_2660] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.1; simp only [constraint_2661] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.1; simp only [constraint_2662] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2663] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2664] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2665] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2666] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2667] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2668] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2669] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2670] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2671] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2672] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2673] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2674] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2675] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2676] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2677] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2678] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2679] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2680] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2681] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2682] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2683] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2684] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2685] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2686] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2687] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2688] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2689] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2690] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2691] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2692] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2693] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2694] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2695] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2696] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2697] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2698] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2699] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2700] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2701] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2702] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2703] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2704] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2705] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2706] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2707] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2708] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2709] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2710] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2711] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2712] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2713] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2714] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2715] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2716] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2717] at hc; linear_combination hc

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_parity_2_eq_extract
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_parity_2 c row)) (j : ℕ) (hj : j < 64) :
    let idx := 128 + j
    let sum5 := a_prime_bit c idx row + a_prime_bit c (idx + 320) row +
                a_prime_bit c (idx + 640) row + a_prime_bit c (idx + 960) row +
                a_prime_bit c (idx + 1280) row
    let diff := sum5 - c_prime_bit c idx row
    diff * (diff - 2) * (diff - 4) = 0 := by
  simp only [seg_E_parity_2, List.forall_cons, id_eq] at h
  interval_cases j
  · have hc := h.1; simp only [constraint_2718] at hc; linear_combination hc
  · have hc := h.2.1; simp only [constraint_2719] at hc; linear_combination hc
  · have hc := h.2.2.1; simp only [constraint_2720] at hc; linear_combination hc
  · have hc := h.2.2.2.1; simp only [constraint_2721] at hc; linear_combination hc
  · have hc := h.2.2.2.2.1; simp only [constraint_2722] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.1; simp only [constraint_2723] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.1; simp only [constraint_2724] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.1; simp only [constraint_2725] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.1; simp only [constraint_2726] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2727] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2728] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2729] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2730] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2731] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2732] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2733] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2734] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2735] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2736] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2737] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2738] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2739] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2740] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2741] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2742] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2743] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2744] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2745] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2746] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2747] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2748] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2749] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2750] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2751] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2752] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2753] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2754] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2755] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2756] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2757] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2758] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2759] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2760] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2761] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2762] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2763] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2764] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2765] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2766] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2767] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2768] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2769] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2770] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2771] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2772] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2773] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2774] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2775] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2776] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2777] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2778] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2779] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2780] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2781] at hc; linear_combination hc

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_parity_3_eq_extract
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_parity_3 c row)) (j : ℕ) (hj : j < 64) :
    let idx := 192 + j
    let sum5 := a_prime_bit c idx row + a_prime_bit c (idx + 320) row +
                a_prime_bit c (idx + 640) row + a_prime_bit c (idx + 960) row +
                a_prime_bit c (idx + 1280) row
    let diff := sum5 - c_prime_bit c idx row
    diff * (diff - 2) * (diff - 4) = 0 := by
  simp only [seg_E_parity_3, List.forall_cons, id_eq] at h
  interval_cases j
  · have hc := h.1; simp only [constraint_2782] at hc; linear_combination hc
  · have hc := h.2.1; simp only [constraint_2783] at hc; linear_combination hc
  · have hc := h.2.2.1; simp only [constraint_2784] at hc; linear_combination hc
  · have hc := h.2.2.2.1; simp only [constraint_2785] at hc; linear_combination hc
  · have hc := h.2.2.2.2.1; simp only [constraint_2786] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.1; simp only [constraint_2787] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.1; simp only [constraint_2788] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.1; simp only [constraint_2789] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.1; simp only [constraint_2790] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2791] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2792] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2793] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2794] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2795] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2796] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2797] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2798] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2799] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2800] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2801] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2802] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2803] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2804] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2805] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2806] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2807] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2808] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2809] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2810] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2811] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2812] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2813] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2814] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2815] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2816] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2817] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2818] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2819] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2820] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2821] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2822] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2823] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2824] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2825] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2826] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2827] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2828] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2829] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2830] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2831] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2832] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2833] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2834] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2835] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2836] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2837] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2838] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2839] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2840] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2841] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2842] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2843] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2844] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2845] at hc; linear_combination hc

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12800000 in
lemma seg_E_parity_4_eq_extract
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_parity_4 c row)) (j : ℕ) (hj : j < 64) :
    let idx := 256 + j
    let sum5 := a_prime_bit c idx row + a_prime_bit c (idx + 320) row +
                a_prime_bit c (idx + 640) row + a_prime_bit c (idx + 960) row +
                a_prime_bit c (idx + 1280) row
    let diff := sum5 - c_prime_bit c idx row
    diff * (diff - 2) * (diff - 4) = 0 := by
  simp only [seg_E_parity_4, List.forall_cons, id_eq] at h
  interval_cases j
  · have hc := h.1; simp only [constraint_2846] at hc; linear_combination hc
  · have hc := h.2.1; simp only [constraint_2847] at hc; linear_combination hc
  · have hc := h.2.2.1; simp only [constraint_2848] at hc; linear_combination hc
  · have hc := h.2.2.2.1; simp only [constraint_2849] at hc; linear_combination hc
  · have hc := h.2.2.2.2.1; simp only [constraint_2850] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.1; simp only [constraint_2851] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.1; simp only [constraint_2852] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.1; simp only [constraint_2853] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.1; simp only [constraint_2854] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2855] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2856] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2857] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2858] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2859] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2860] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2861] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2862] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2863] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2864] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2865] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2866] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2867] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2868] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2869] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2870] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2871] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2872] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2873] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2874] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2875] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2876] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2877] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2878] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2879] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2880] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2881] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2882] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2883] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2884] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2885] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2886] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2887] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2888] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2889] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2890] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2891] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2892] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2893] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2894] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2895] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2896] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2897] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2898] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2899] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2900] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2901] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2902] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2903] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2904] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2905] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2906] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2907] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2908] at hc; linear_combination hc
  · have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp only [constraint_2909] at hc; linear_combination hc

set_option maxHeartbeats 800000 in
lemma chiConstraints_of_seg_E_chi
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_chi c row)) :
    ChiConstraints c row := by
  simp only [seg_E_chi, List.forall_cons, id_eq] at h
  exact {
    h2910 := h.1,
    h2911 := h.2.1,
    h2912 := h.2.2.1,
    h2913 := h.2.2.2.1,
    h2914 := h.2.2.2.2.1,
    h2915 := h.2.2.2.2.2.1,
    h2916 := h.2.2.2.2.2.2.1,
    h2917 := h.2.2.2.2.2.2.2.1,
    h2918 := h.2.2.2.2.2.2.2.2.1,
    h2919 := h.2.2.2.2.2.2.2.2.2.1,
    h2920 := h.2.2.2.2.2.2.2.2.2.2.1,
    h2921 := h.2.2.2.2.2.2.2.2.2.2.2.1,
    h2922 := h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2923 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2924 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2925 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2926 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2927 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2928 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2929 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2930 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2931 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2932 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2933 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2934 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2935 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2936 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2937 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2938 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2939 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2940 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2941 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2942 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2943 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2944 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2945 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2946 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2947 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2948 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2949 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2950 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2951 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2952 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2953 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2954 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2955 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2956 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2957 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2958 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2959 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2960 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2961 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2962 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2963 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2964 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2965 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2966 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2967 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2968 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2969 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2970 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2971 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2972 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2973 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2974 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2975 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2976 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2977 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2978 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2979 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2980 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2981 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2982 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2983 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2984 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2985 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2986 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2987 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2988 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2989 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2990 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2991 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2992 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2993 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2994 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2995 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2996 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2997 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2998 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h2999 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h3000 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h3001 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h3002 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h3003 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h3004 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h3005 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h3006 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h3007 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h3008 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h3009 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  }

/-!
  ## Local helper: forall_range_map
-/

private lemma forall_id_mem' {l : List Prop} (h : List.Forall id l)
    {p : Prop} (hp : p ∈ l) : p :=
  List.forall_iff_forall_mem.mp h p hp

private lemma forall_range_map' {n : ℕ} {f : ℕ → Prop}
    (h : List.Forall id ((List.range n).map f)) {i : ℕ} (hi : i < n) : f i :=
  forall_id_mem' h (List.mem_map_of_mem (List.mem_range.mpr hi))

/-!
  ## Per-field helper lemmas: seg_E → RoundLocalConstraints fields
-/

-- 1. c_bit_bool: ∀ i < 320, c_bit bool constraint
-- Dispatch across 5 blocks: cbits_0(0-63), cbits_2(64-127), cbits_4(128-191),
--                            cprime_1(192-255), cprime_3(256-319)
set_option maxHeartbeats 6400000 in
lemma c_bit_bool_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    ∀ i, i < 320 → c_bit c i row * (c_bit c i row - 1) = 0 := by
  obtain ⟨_, h_cb, h_cp, _, _, _, _, _, _, _, _, _, _⟩ := seg_E_forall_parts c row h
  rw [seg_E_cbits_eq_chunks] at h_cb
  simp only [List.forall_append] at h_cb
  obtain ⟨⟨⟨⟨h_cb0, h_cb1⟩, h_cb2⟩, h_cb3⟩, h_cb4⟩ := h_cb
  rw [seg_E_cprime_eq_chunks] at h_cp
  simp only [List.forall_append] at h_cp
  obtain ⟨⟨⟨⟨h_cp0, h_cp1⟩, h_cp2⟩, h_cp3⟩, h_cp4⟩ := h_cp
  intro i hi
  rcases Nat.lt_or_ge i 64 with h1 | h1
  · rw [seg_E_cbits_0_eq_map] at h_cb0
    have := forall_range_map' h_cb0 h1
    simp only [Nat.zero_add] at this; exact this
  · rcases Nat.lt_or_ge i 128 with h2 | h2
    · rw [seg_E_cbits_2_eq_map] at h_cb2
      have := forall_range_map' h_cb2 (show i - 64 < 64 by omega)
      have h_idx : 64 + (i - 64) = i := by omega
      simp only [h_idx] at this; exact this
    · rcases Nat.lt_or_ge i 192 with h3 | h3
      · rw [seg_E_cbits_4_eq_map] at h_cb4
        have := forall_range_map' h_cb4 (show i - 128 < 64 by omega)
        have h_idx : 128 + (i - 128) = i := by omega
        simp only [h_idx] at this; exact this
      · rcases Nat.lt_or_ge i 256 with h4 | h4
        · rw [seg_E_cprime_1_eq_map] at h_cp1
          have := forall_range_map' h_cp1 (show i - 192 < 64 by omega)
          have h_idx : 192 + (i - 192) = i := by omega
          simp only [h_idx] at this; exact this
        · rw [seg_E_cprime_3_eq_map] at h_cp3
          have := forall_range_map' h_cp3 (show i - 256 < 64 by omega)
          have h_idx : 256 + (i - 256) = i := by omega
          simp only [h_idx] at this; exact this

-- 2. c_prime_def: ∀ i < 320, c_prime_bit definition constraint
-- Dispatch across 5 blocks: cbits_1(0-63), cbits_3(64-127), cprime_0(128-191),
--                            cprime_2(192-255), cprime_4(256-319)
set_option maxHeartbeats 6400000 in
lemma c_prime_def_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    ∀ i, i < 320 →
      let x := i / 64
      let z := i % 64
      let left_idx := 64 * ((x + 4) % 5) + z
      let right_shift_idx := 64 * ((x + 1) % 5) + (z + 63) % 64
      (c_prime_bit c i row) -
        fieldXor (fieldXor (c_bit c i row) (c_bit c left_idx row))
                 (c_bit c right_shift_idx row) = 0 := by
  obtain ⟨_, h_cb, h_cp, _, _, _, _, _, _, _, _, _, _⟩ := seg_E_forall_parts c row h
  rw [seg_E_cbits_eq_chunks] at h_cb
  simp only [List.forall_append] at h_cb
  obtain ⟨⟨⟨⟨h_cb0, h_cb1⟩, h_cb2⟩, h_cb3⟩, h_cb4⟩ := h_cb
  rw [seg_E_cprime_eq_chunks] at h_cp
  simp only [List.forall_append] at h_cp
  obtain ⟨⟨⟨⟨h_cp0, h_cp1⟩, h_cp2⟩, h_cp3⟩, h_cp4⟩ := h_cp
  intro i hi
  rcases Nat.lt_or_ge i 64 with h1 | h1
  · have := seg_E_cbits_1_eq_extract c row h_cb1 i h1
    simp only [show 0 + i = i from by omega] at this; exact this
  · rcases Nat.lt_or_ge i 128 with h2 | h2
    · have := seg_E_cbits_3_eq_extract c row h_cb3 (i - 64) (by omega)
      simp only [show 64 + (i - 64) = i from by omega] at this; exact this
    · rcases Nat.lt_or_ge i 192 with h3 | h3
      · have := seg_E_cprime_0_eq_extract c row h_cp0 (i - 128) (by omega)
        simp only [show 128 + (i - 128) = i from by omega] at this; exact this
      · rcases Nat.lt_or_ge i 256 with h4 | h4
        · have := seg_E_cprime_2_eq_extract c row h_cp2 (i - 192) (by omega)
          simp only [show 192 + (i - 192) = i from by omega] at this; exact this
        · have := seg_E_cprime_4_eq_extract c row h_cp4 (i - 256) (by omega)
          simp only [show 256 + (i - 256) = i from by omega] at this; exact this

-- 3. a_prime_bit_bool: ∀ i < 1600, dispatch across 25 blocks (5 groups × 5 blocks)
-- Split into 5 sub-helpers (one per AP group) to keep compile time manageable.

set_option maxHeartbeats 6400000 in
private lemma a_prime_bit_bool_of_ap_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_ap_0 c row))
    (i : ℕ) (hi : i < 320) :
    a_prime_bit c i row * (a_prime_bit c i row - 1) = 0 := by
  rw [seg_E_ap_0_eq_chunks] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, _⟩, hb1⟩, _⟩, hb2⟩, _⟩, hb3⟩, _⟩, hb4⟩, _⟩ := h
  rcases Nat.lt_or_ge i 64 with h1 | h1
  · rw [seg_E_ap_0_bool_0_eq_map] at hb0
    have := forall_range_map' hb0 h1
    simp only [Nat.zero_add] at this; exact this
  · rcases Nat.lt_or_ge i 128 with h2 | h2
    · rw [seg_E_ap_0_bool_1_eq_map] at hb1
      have := forall_range_map' hb1 (show i - 64 < 64 by omega)
      have h_idx : 64 + (i - 64) = i := by omega
      simp only [h_idx] at this; exact this
    · rcases Nat.lt_or_ge i 192 with h3 | h3
      · rw [seg_E_ap_0_bool_2_eq_map] at hb2
        have := forall_range_map' hb2 (show i - 128 < 64 by omega)
        have h_idx : 128 + (i - 128) = i := by omega
        simp only [h_idx] at this; exact this
      · rcases Nat.lt_or_ge i 256 with h4 | h4
        · rw [seg_E_ap_0_bool_3_eq_map] at hb3
          have := forall_range_map' hb3 (show i - 192 < 64 by omega)
          have h_idx : 192 + (i - 192) = i := by omega
          simp only [h_idx] at this; exact this
        · rw [seg_E_ap_0_bool_4_eq_map] at hb4
          have := forall_range_map' hb4 (show i - 256 < 64 by omega)
          have h_idx : 256 + (i - 256) = i := by omega
          simp only [h_idx] at this; exact this

set_option maxHeartbeats 6400000 in
private lemma a_prime_bit_bool_of_ap_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_ap_1 c row))
    (i : ℕ) (hi_lo : 320 ≤ i) (hi_hi : i < 640) :
    a_prime_bit c i row * (a_prime_bit c i row - 1) = 0 := by
  rw [seg_E_ap_1_eq_chunks] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, _⟩, hb1⟩, _⟩, hb2⟩, _⟩, hb3⟩, _⟩, hb4⟩, _⟩ := h
  rcases Nat.lt_or_ge i 384 with h1 | h1
  · rw [seg_E_ap_1_bool_0_eq_map] at hb0
    have := forall_range_map' hb0 (show i - 320 < 64 by omega)
    have h_idx : 320 + (i - 320) = i := by omega
    simp only [h_idx] at this; exact this
  · rcases Nat.lt_or_ge i 448 with h2 | h2
    · rw [seg_E_ap_1_bool_1_eq_map] at hb1
      have := forall_range_map' hb1 (show i - 384 < 64 by omega)
      have h_idx : 384 + (i - 384) = i := by omega
      simp only [h_idx] at this; exact this
    · rcases Nat.lt_or_ge i 512 with h3 | h3
      · rw [seg_E_ap_1_bool_2_eq_map] at hb2
        have := forall_range_map' hb2 (show i - 448 < 64 by omega)
        have h_idx : 448 + (i - 448) = i := by omega
        simp only [h_idx] at this; exact this
      · rcases Nat.lt_or_ge i 576 with h4 | h4
        · rw [seg_E_ap_1_bool_3_eq_map] at hb3
          have := forall_range_map' hb3 (show i - 512 < 64 by omega)
          have h_idx : 512 + (i - 512) = i := by omega
          simp only [h_idx] at this; exact this
        · rw [seg_E_ap_1_bool_4_eq_map] at hb4
          have := forall_range_map' hb4 (show i - 576 < 64 by omega)
          have h_idx : 576 + (i - 576) = i := by omega
          simp only [h_idx] at this; exact this

set_option maxHeartbeats 6400000 in
private lemma a_prime_bit_bool_of_ap_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_ap_2 c row))
    (i : ℕ) (hi_lo : 640 ≤ i) (hi_hi : i < 960) :
    a_prime_bit c i row * (a_prime_bit c i row - 1) = 0 := by
  rw [seg_E_ap_2_eq_chunks] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, _⟩, hb1⟩, _⟩, hb2⟩, _⟩, hb3⟩, _⟩, hb4⟩, _⟩ := h
  rcases Nat.lt_or_ge i 704 with h1 | h1
  · rw [seg_E_ap_2_bool_0_eq_map] at hb0
    have := forall_range_map' hb0 (show i - 640 < 64 by omega)
    have h_idx : 640 + (i - 640) = i := by omega
    simp only [h_idx] at this; exact this
  · rcases Nat.lt_or_ge i 768 with h2 | h2
    · rw [seg_E_ap_2_bool_1_eq_map] at hb1
      have := forall_range_map' hb1 (show i - 704 < 64 by omega)
      have h_idx : 704 + (i - 704) = i := by omega
      simp only [h_idx] at this; exact this
    · rcases Nat.lt_or_ge i 832 with h3 | h3
      · rw [seg_E_ap_2_bool_2_eq_map] at hb2
        have := forall_range_map' hb2 (show i - 768 < 64 by omega)
        have h_idx : 768 + (i - 768) = i := by omega
        simp only [h_idx] at this; exact this
      · rcases Nat.lt_or_ge i 896 with h4 | h4
        · rw [seg_E_ap_2_bool_3_eq_map] at hb3
          have := forall_range_map' hb3 (show i - 832 < 64 by omega)
          have h_idx : 832 + (i - 832) = i := by omega
          simp only [h_idx] at this; exact this
        · rw [seg_E_ap_2_bool_4_eq_map] at hb4
          have := forall_range_map' hb4 (show i - 896 < 64 by omega)
          have h_idx : 896 + (i - 896) = i := by omega
          simp only [h_idx] at this; exact this

set_option maxHeartbeats 6400000 in
private lemma a_prime_bit_bool_of_ap_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_ap_3 c row))
    (i : ℕ) (hi_lo : 960 ≤ i) (hi_hi : i < 1280) :
    a_prime_bit c i row * (a_prime_bit c i row - 1) = 0 := by
  rw [seg_E_ap_3_eq_chunks] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, _⟩, hb1⟩, _⟩, hb2⟩, _⟩, hb3⟩, _⟩, hb4⟩, _⟩ := h
  rcases Nat.lt_or_ge i 1024 with h1 | h1
  · rw [seg_E_ap_3_bool_0_eq_map] at hb0
    have := forall_range_map' hb0 (show i - 960 < 64 by omega)
    have h_idx : 960 + (i - 960) = i := by omega
    simp only [h_idx] at this; exact this
  · rcases Nat.lt_or_ge i 1088 with h2 | h2
    · rw [seg_E_ap_3_bool_1_eq_map] at hb1
      have := forall_range_map' hb1 (show i - 1024 < 64 by omega)
      have h_idx : 1024 + (i - 1024) = i := by omega
      simp only [h_idx] at this; exact this
    · rcases Nat.lt_or_ge i 1152 with h3 | h3
      · rw [seg_E_ap_3_bool_2_eq_map] at hb2
        have := forall_range_map' hb2 (show i - 1088 < 64 by omega)
        have h_idx : 1088 + (i - 1088) = i := by omega
        simp only [h_idx] at this; exact this
      · rcases Nat.lt_or_ge i 1216 with h4 | h4
        · rw [seg_E_ap_3_bool_3_eq_map] at hb3
          have := forall_range_map' hb3 (show i - 1152 < 64 by omega)
          have h_idx : 1152 + (i - 1152) = i := by omega
          simp only [h_idx] at this; exact this
        · rw [seg_E_ap_3_bool_4_eq_map] at hb4
          have := forall_range_map' hb4 (show i - 1216 < 64 by omega)
          have h_idx : 1216 + (i - 1216) = i := by omega
          simp only [h_idx] at this; exact this

set_option maxHeartbeats 6400000 in
private lemma a_prime_bit_bool_of_ap_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_ap_4 c row))
    (i : ℕ) (hi_lo : 1280 ≤ i) (hi_hi : i < 1600) :
    a_prime_bit c i row * (a_prime_bit c i row - 1) = 0 := by
  rw [seg_E_ap_4_eq_chunks] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, _⟩, hb1⟩, _⟩, hb2⟩, _⟩, hb3⟩, _⟩, hb4⟩, _⟩ := h
  rcases Nat.lt_or_ge i 1344 with h1 | h1
  · rw [seg_E_ap_4_bool_0_eq_map] at hb0
    have := forall_range_map' hb0 (show i - 1280 < 64 by omega)
    have h_idx : 1280 + (i - 1280) = i := by omega
    simp only [h_idx] at this; exact this
  · rcases Nat.lt_or_ge i 1408 with h2 | h2
    · rw [seg_E_ap_4_bool_1_eq_map] at hb1
      have := forall_range_map' hb1 (show i - 1344 < 64 by omega)
      have h_idx : 1344 + (i - 1344) = i := by omega
      simp only [h_idx] at this; exact this
    · rcases Nat.lt_or_ge i 1472 with h3 | h3
      · rw [seg_E_ap_4_bool_2_eq_map] at hb2
        have := forall_range_map' hb2 (show i - 1408 < 64 by omega)
        have h_idx : 1408 + (i - 1408) = i := by omega
        simp only [h_idx] at this; exact this
      · rcases Nat.lt_or_ge i 1536 with h4 | h4
        · rw [seg_E_ap_4_bool_3_eq_map] at hb3
          have := forall_range_map' hb3 (show i - 1472 < 64 by omega)
          have h_idx : 1472 + (i - 1472) = i := by omega
          simp only [h_idx] at this; exact this
        · rw [seg_E_ap_4_bool_4_eq_map] at hb4
          have := forall_range_map' hb4 (show i - 1536 < 64 by omega)
          have h_idx : 1536 + (i - 1536) = i := by omega
          simp only [h_idx] at this; exact this

set_option maxHeartbeats 6400000 in
lemma a_prime_bit_bool_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    ∀ i, i < 1600 → a_prime_bit c i row * (a_prime_bit c i row - 1) = 0 := by
  obtain ⟨_, _, _, h_a0, h_a1, h_a2, h_a3, h_a4, _, _, _, _, _⟩ := seg_E_forall_parts c row h
  intro i hi
  rcases Nat.lt_or_ge i 320 with h1 | h1
  · exact a_prime_bit_bool_of_ap_0 c row h_a0 i h1
  · rcases Nat.lt_or_ge i 640 with h2 | h2
    · exact a_prime_bit_bool_of_ap_1 c row h_a1 i (by omega) h2
    · rcases Nat.lt_or_ge i 960 with h3 | h3
      · exact a_prime_bit_bool_of_ap_2 c row h_a2 i (by omega) h3
      · rcases Nat.lt_or_ge i 1280 with h4 | h4
        · exact a_prime_bit_bool_of_ap_3 c row h_a3 i (by omega) h4
        · exact a_prime_bit_bool_of_ap_4 c row h_a4 i (by omega) (by omega)

-- 4. theta_xor3_recompose: ∀ j < 100, dispatch across 25 xor3 blocks
-- Split into 5 sub-helpers (one per AP group).

set_option maxHeartbeats 6400000 in
private lemma theta_xor3_of_ap_0
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_ap_0 c row))
    (j : ℕ) (hj : j < 20) :
    let x := (j / 4) % 5
    let limb := j % 4
    KeccakfPermAir.extraction.xor3_recompose16_eq c
      (225 + 64 * x + 16 * limb) (545 + 64 * x + 16 * limb)
      (865 + 16 * j) (125 + j) row := by
  rw [seg_E_ap_0_eq_chunks] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hx0⟩, _⟩, hx1⟩, _⟩, hx2⟩, _⟩, hx3⟩, _⟩, hx4⟩ := h
  rcases Nat.lt_or_ge j 4 with h1 | h1
  · rw [seg_E_ap_0_xor3_0_eq_map] at hx0
    have := forall_range_map' hx0 (show j < 4 by omega)
    simp only [show 0 + j = j from by omega] at this; exact this
  · rcases Nat.lt_or_ge j 8 with h2 | h2
    · rw [seg_E_ap_0_xor3_1_eq_map] at hx1
      have := forall_range_map' hx1 (show j - 4 < 4 by omega)
      simp only [show 4 + (j - 4) = j from by omega] at this; exact this
    · rcases Nat.lt_or_ge j 12 with h3 | h3
      · rw [seg_E_ap_0_xor3_2_eq_map] at hx2
        have := forall_range_map' hx2 (show j - 8 < 4 by omega)
        simp only [show 8 + (j - 8) = j from by omega] at this; exact this
      · rcases Nat.lt_or_ge j 16 with h4 | h4
        · rw [seg_E_ap_0_xor3_3_eq_map] at hx3
          have := forall_range_map' hx3 (show j - 12 < 4 by omega)
          simp only [show 12 + (j - 12) = j from by omega] at this; exact this
        · rw [seg_E_ap_0_xor3_4_eq_map] at hx4
          have := forall_range_map' hx4 (show j - 16 < 4 by omega)
          simp only [show 16 + (j - 16) = j from by omega] at this; exact this

set_option maxHeartbeats 6400000 in
private lemma theta_xor3_of_ap_1
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_ap_1 c row))
    (j : ℕ) (hj_lo : 20 ≤ j) (hj_hi : j < 40) :
    let x := (j / 4) % 5
    let limb := j % 4
    KeccakfPermAir.extraction.xor3_recompose16_eq c
      (225 + 64 * x + 16 * limb) (545 + 64 * x + 16 * limb)
      (865 + 16 * j) (125 + j) row := by
  rw [seg_E_ap_1_eq_chunks] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hx0⟩, _⟩, hx1⟩, _⟩, hx2⟩, _⟩, hx3⟩, _⟩, hx4⟩ := h
  rcases Nat.lt_or_ge j 24 with h1 | h1
  · rw [seg_E_ap_1_xor3_0_eq_map] at hx0
    have := forall_range_map' hx0 (show j - 20 < 4 by omega)
    simp only [show 20 + (j - 20) = j from by omega] at this; exact this
  · rcases Nat.lt_or_ge j 28 with h2 | h2
    · rw [seg_E_ap_1_xor3_1_eq_map] at hx1
      have := forall_range_map' hx1 (show j - 24 < 4 by omega)
      simp only [show 24 + (j - 24) = j from by omega] at this; exact this
    · rcases Nat.lt_or_ge j 32 with h3 | h3
      · rw [seg_E_ap_1_xor3_2_eq_map] at hx2
        have := forall_range_map' hx2 (show j - 28 < 4 by omega)
        simp only [show 28 + (j - 28) = j from by omega] at this; exact this
      · rcases Nat.lt_or_ge j 36 with h4 | h4
        · rw [seg_E_ap_1_xor3_3_eq_map] at hx3
          have := forall_range_map' hx3 (show j - 32 < 4 by omega)
          simp only [show 32 + (j - 32) = j from by omega] at this; exact this
        · rw [seg_E_ap_1_xor3_4_eq_map] at hx4
          have := forall_range_map' hx4 (show j - 36 < 4 by omega)
          simp only [show 36 + (j - 36) = j from by omega] at this; exact this

set_option maxHeartbeats 6400000 in
private lemma theta_xor3_of_ap_2
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_ap_2 c row))
    (j : ℕ) (hj_lo : 40 ≤ j) (hj_hi : j < 60) :
    let x := (j / 4) % 5
    let limb := j % 4
    KeccakfPermAir.extraction.xor3_recompose16_eq c
      (225 + 64 * x + 16 * limb) (545 + 64 * x + 16 * limb)
      (865 + 16 * j) (125 + j) row := by
  rw [seg_E_ap_2_eq_chunks] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hx0⟩, _⟩, hx1⟩, _⟩, hx2⟩, _⟩, hx3⟩, _⟩, hx4⟩ := h
  rcases Nat.lt_or_ge j 44 with h1 | h1
  · rw [seg_E_ap_2_xor3_0_eq_map] at hx0
    have := forall_range_map' hx0 (show j - 40 < 4 by omega)
    simp only [show 40 + (j - 40) = j from by omega] at this; exact this
  · rcases Nat.lt_or_ge j 48 with h2 | h2
    · rw [seg_E_ap_2_xor3_1_eq_map] at hx1
      have := forall_range_map' hx1 (show j - 44 < 4 by omega)
      simp only [show 44 + (j - 44) = j from by omega] at this; exact this
    · rcases Nat.lt_or_ge j 52 with h3 | h3
      · rw [seg_E_ap_2_xor3_2_eq_map] at hx2
        have := forall_range_map' hx2 (show j - 48 < 4 by omega)
        simp only [show 48 + (j - 48) = j from by omega] at this; exact this
      · rcases Nat.lt_or_ge j 56 with h4 | h4
        · rw [seg_E_ap_2_xor3_3_eq_map] at hx3
          have := forall_range_map' hx3 (show j - 52 < 4 by omega)
          simp only [show 52 + (j - 52) = j from by omega] at this; exact this
        · rw [seg_E_ap_2_xor3_4_eq_map] at hx4
          have := forall_range_map' hx4 (show j - 56 < 4 by omega)
          simp only [show 56 + (j - 56) = j from by omega] at this; exact this

set_option maxHeartbeats 6400000 in
private lemma theta_xor3_of_ap_3
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_ap_3 c row))
    (j : ℕ) (hj_lo : 60 ≤ j) (hj_hi : j < 80) :
    let x := (j / 4) % 5
    let limb := j % 4
    KeccakfPermAir.extraction.xor3_recompose16_eq c
      (225 + 64 * x + 16 * limb) (545 + 64 * x + 16 * limb)
      (865 + 16 * j) (125 + j) row := by
  rw [seg_E_ap_3_eq_chunks] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hx0⟩, _⟩, hx1⟩, _⟩, hx2⟩, _⟩, hx3⟩, _⟩, hx4⟩ := h
  rcases Nat.lt_or_ge j 64 with h1 | h1
  · rw [seg_E_ap_3_xor3_0_eq_map] at hx0
    have := forall_range_map' hx0 (show j - 60 < 4 by omega)
    simp only [show 60 + (j - 60) = j from by omega] at this; exact this
  · rcases Nat.lt_or_ge j 68 with h2 | h2
    · rw [seg_E_ap_3_xor3_1_eq_map] at hx1
      have := forall_range_map' hx1 (show j - 64 < 4 by omega)
      simp only [show 64 + (j - 64) = j from by omega] at this; exact this
    · rcases Nat.lt_or_ge j 72 with h3 | h3
      · rw [seg_E_ap_3_xor3_2_eq_map] at hx2
        have := forall_range_map' hx2 (show j - 68 < 4 by omega)
        simp only [show 68 + (j - 68) = j from by omega] at this; exact this
      · rcases Nat.lt_or_ge j 76 with h4 | h4
        · rw [seg_E_ap_3_xor3_3_eq_map] at hx3
          have := forall_range_map' hx3 (show j - 72 < 4 by omega)
          simp only [show 72 + (j - 72) = j from by omega] at this; exact this
        · rw [seg_E_ap_3_xor3_4_eq_map] at hx4
          have := forall_range_map' hx4 (show j - 76 < 4 by omega)
          simp only [show 76 + (j - 76) = j from by omega] at this; exact this

set_option maxHeartbeats 6400000 in
private lemma theta_xor3_of_ap_4
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E_ap_4 c row))
    (j : ℕ) (hj_lo : 80 ≤ j) (hj_hi : j < 100) :
    let x := (j / 4) % 5
    let limb := j % 4
    KeccakfPermAir.extraction.xor3_recompose16_eq c
      (225 + 64 * x + 16 * limb) (545 + 64 * x + 16 * limb)
      (865 + 16 * j) (125 + j) row := by
  rw [seg_E_ap_4_eq_chunks] at h
  simp only [List.forall_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hx0⟩, _⟩, hx1⟩, _⟩, hx2⟩, _⟩, hx3⟩, _⟩, hx4⟩ := h
  rcases Nat.lt_or_ge j 84 with h1 | h1
  · rw [seg_E_ap_4_xor3_0_eq_map] at hx0
    have := forall_range_map' hx0 (show j - 80 < 4 by omega)
    simp only [show 80 + (j - 80) = j from by omega] at this; exact this
  · rcases Nat.lt_or_ge j 88 with h2 | h2
    · rw [seg_E_ap_4_xor3_1_eq_map] at hx1
      have := forall_range_map' hx1 (show j - 84 < 4 by omega)
      simp only [show 84 + (j - 84) = j from by omega] at this; exact this
    · rcases Nat.lt_or_ge j 92 with h3 | h3
      · rw [seg_E_ap_4_xor3_2_eq_map] at hx2
        have := forall_range_map' hx2 (show j - 88 < 4 by omega)
        simp only [show 88 + (j - 88) = j from by omega] at this; exact this
      · rcases Nat.lt_or_ge j 96 with h4 | h4
        · rw [seg_E_ap_4_xor3_3_eq_map] at hx3
          have := forall_range_map' hx3 (show j - 92 < 4 by omega)
          simp only [show 92 + (j - 92) = j from by omega] at this; exact this
        · rw [seg_E_ap_4_xor3_4_eq_map] at hx4
          have := forall_range_map' hx4 (show j - 96 < 4 by omega)
          simp only [show 96 + (j - 96) = j from by omega] at this; exact this

set_option maxHeartbeats 6400000 in
lemma theta_xor3_recompose_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    ∀ j, j < 100 →
      let x := (j / 4) % 5
      let limb := j % 4
      KeccakfPermAir.extraction.xor3_recompose16_eq c
        (225 + 64 * x + 16 * limb) (545 + 64 * x + 16 * limb)
        (865 + 16 * j) (125 + j) row := by
  obtain ⟨_, _, _, h_a0, h_a1, h_a2, h_a3, h_a4, _, _, _, _, _⟩ := seg_E_forall_parts c row h
  intro j hj
  rcases Nat.lt_or_ge j 20 with h1 | h1
  · exact theta_xor3_of_ap_0 c row h_a0 j h1
  · rcases Nat.lt_or_ge j 40 with h2 | h2
    · exact theta_xor3_of_ap_1 c row h_a1 j (by omega) h2
    · rcases Nat.lt_or_ge j 60 with h3 | h3
      · exact theta_xor3_of_ap_2 c row h_a2 j (by omega) h3
      · rcases Nat.lt_or_ge j 80 with h4 | h4
        · exact theta_xor3_of_ap_3 c row h_a3 j (by omega) h4
        · exact theta_xor3_of_ap_4 c row h_a4 j (by omega) (by omega)

-- 5. theta_parity: ∀ i < 320, dispatch across 5 parity blocks
set_option maxHeartbeats 6400000 in
lemma theta_parity_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    ∀ i, i < 320 →
      let sum5 := a_prime_bit c i row + a_prime_bit c (i + 320) row +
                  a_prime_bit c (i + 640) row + a_prime_bit c (i + 960) row +
                  a_prime_bit c (i + 1280) row
      let diff := sum5 - c_prime_bit c i row
      diff * (diff - 2) * (diff - 4) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, h_pa, _, _, _, _⟩ := seg_E_forall_parts c row h
  rw [seg_E_parity_eq_chunks] at h_pa
  simp only [List.forall_append] at h_pa
  obtain ⟨⟨⟨⟨hp0, hp1⟩, hp2⟩, hp3⟩, hp4⟩ := h_pa
  intro i hi
  rcases Nat.lt_or_ge i 64 with h1 | h1
  · have := seg_E_parity_0_eq_extract c row hp0 i h1
    simp only [show 0 + i = i from by omega] at this; exact this
  · rcases Nat.lt_or_ge i 128 with h2 | h2
    · have := seg_E_parity_1_eq_extract c row hp1 (i - 64) (by omega)
      simp only [show 64 + (i - 64) = i from by omega] at this; exact this
    · rcases Nat.lt_or_ge i 192 with h3 | h3
      · have := seg_E_parity_2_eq_extract c row hp2 (i - 128) (by omega)
        simp only [show 128 + (i - 128) = i from by omega] at this; exact this
      · rcases Nat.lt_or_ge i 256 with h4 | h4
        · have := seg_E_parity_3_eq_extract c row hp3 (i - 192) (by omega)
          simp only [show 192 + (i - 192) = i from by omega] at this; exact this
        · have := seg_E_parity_4_eq_extract c row hp4 (i - 256) (by omega)
          simp only [show 256 + (i - 256) = i from by omega] at this; exact this

-- 6. chi: delegates to chiConstraints_of_seg_E_chi
set_option maxHeartbeats 6400000 in
lemma chi_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    ChiConstraints c row := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h_ch, _, _, _⟩ := seg_E_forall_parts c row h
  exact chiConstraints_of_seg_E_chi c row h_ch

-- 7. a_pp_00_bit_bool: ∀ i < 64, from iota_bits
set_option maxHeartbeats 6400000 in
lemma a_pp_00_bit_bool_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    ∀ i, i < 64 → a_pp_00_bit c i row * (a_pp_00_bit c i row - 1) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h_ib, _, _⟩ := seg_E_forall_parts c row h
  rw [seg_E_iota_bits_eq_map] at h_ib
  intro i hi
  exact forall_range_map' h_ib hi

-- 8. iota_preiota_recompose: ∀ k < 4
set_option maxHeartbeats 6400000 in
lemma iota_preiota_recompose_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    ∀ k, k < 4 →
      KeccakfPermAir.extraction.recompose16_eq c (2565 + 16 * k) (2465 + k) row := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h_ir, _⟩ := seg_E_forall_parts c row h
  rw [seg_E_iota_recomp_eq_map] at h_ir
  intro k hk
  exact forall_range_map' h_ir hk

-- 9-12. iota output: individual constraint extraction
set_option maxHeartbeats 6400000 in
lemma iota_output_3078_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    constraint_3078 c row := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h_io⟩ := seg_E_forall_parts c row h
  simp only [seg_E_iota_out, List.forall_cons, id_eq] at h_io
  exact h_io.1

set_option maxHeartbeats 6400000 in
lemma iota_output_3079_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    constraint_3079 c row := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h_io⟩ := seg_E_forall_parts c row h
  simp only [seg_E_iota_out, List.forall_cons, id_eq] at h_io
  exact h_io.2.1

set_option maxHeartbeats 6400000 in
lemma iota_output_3080_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    constraint_3080 c row := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h_io⟩ := seg_E_forall_parts c row h
  simp only [seg_E_iota_out, List.forall_cons, id_eq] at h_io
  exact h_io.2.2.1

set_option maxHeartbeats 6400000 in
lemma iota_output_3081_of_seg_E
    {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row : ℕ)
    (h : List.Forall id (seg_E c row)) :
    constraint_3081 c row := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h_io⟩ := seg_E_forall_parts c row h
  simp only [seg_E_iota_out, List.forall_cons, id_eq] at h_io
  exact h_io.2.2.2.1

end KeccakfPermAir.Soundness

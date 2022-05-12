
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.
From Coq Require Export Numbers.NatInt.NZDiv.
Require Coq.Program.Wf.


(*Arraylist code*)
Fixpoint lookup (l : list nat) (i : nat) := 
    match l with
    | [] => 0
    | h :: t => if i <=? 0 then h else lookup t (i-1)
    end.
   

Example lookup_example1 :
    lookup [2;3;4;5;1;2] 3= 5.
Proof. simpl. reflexivity. Qed.

Example lookup_example_empty_list :
    lookup [] 3= 0.
Proof. simpl. reflexivity. Qed.

Example lookup_example_higher_than_list :
    lookup [2;3;4;5;1;2] 10 = 0.
Proof. simpl. reflexivity. Qed.


Fixpoint insert (elem : nat) (index : nat) (l : list nat) :=
match (index, l) with
| (0, x::xs) => elem :: xs
| (0, []) => [elem] (* should never happen *)
| (n, x::xs) => x :: (insert elem (index-1) xs)
| (n, []) => [elem] (* should never happen *)
end.

Example insert_example1:
    insert 3 1 [2;2;2] = [2;3;2].
Proof.
    trivial.
Qed.

Example insert_example2:
    insert 3 0 [2] = [3].
Proof.
    trivial.
Qed.

(*Shuffle code*)

Definition randnat (seed : nat) (bound : nat) : nat :=
    (seed*31+7) mod bound.

Definition fst3 (tuple : ((list nat)*nat*nat)) : list nat :=
    match tuple with
    | (a,b,c) => a
    end.

Definition swap (l : list nat) (i1 : nat) (i2 : nat) : list nat :=
    insert (lookup l i2) i1 (insert (lookup l i1) i2 l).

Example swap_example1:
    swap [1;2;3;4] 0 3 = [4;2;3;1].
Proof.
    trivial.
Qed.

Example swap_example2:
    swap [1;2;3;4;5] 0 3 = [4;2;3;1;5].
Proof.
    trivial.
Qed.


Definition shuffle (l : list nat) : list nat :=
    fst3 (List.fold_left (fun (acc : ((list nat)*nat*nat)) (a : nat) =>
            match acc with
            | (li,seed,point) => (swap li point (randnat seed (List.length li)) ,seed+1,point+1)
            end) l (l,42,0)).

Example shuffle_example1:
    shuffle [1;2;3;4;5] = [2;3;4;1;5]. (*pseudorandom order*)
Proof.
    reflexivity.
Qed.

Program Fixpoint partition_left (l : list nat) (pivot : nat) (lo : nat) (hi : nat) {measure (hi-lo)} : nat :=
    match hi <=? lo with
        | true => lo
        | false => match (lookup l lo <=? pivot) with
            | true => partition_left l pivot (lo+1) hi
            | false => lo
    end end.
Next Obligation.
    symmetry in Heq_anonymous0. apply leb_complete_conv in Heq_anonymous0.
    lia.
Qed.

Example partition_left_example1:
    partition_left [1;2;3;4;5] 1 0 4 = 1.
Proof.
    reflexivity.
Qed.

Program Fixpoint partition_right (l : list nat) (pivot : nat) (lo : nat) (hi : nat) {measure (hi-lo)} : nat :=
    match hi <=? lo with
        | true => hi
        | false => match (pivot <=? lookup l hi) with
            | true => partition_right l pivot lo (hi-1)
            | false => hi
    end end.
Next Obligation.
    symmetry in Heq_anonymous0. apply leb_complete_conv in Heq_anonymous0.
    lia.
Qed.

Example partition_right_example1:
    partition_right [1;2;3;4;5] 1 0 4 = 0.
Proof.
    reflexivity.
Qed.

Lemma helper : forall pr pl hi lo, pr <= hi -> pl >= lo -> pl < pr -> pr - 1 - (pl + 1) < hi - lo.
Proof. intros. lia.
Qed. 

Program Fixpoint partition (l : list nat) (pivot : nat) (lo : nat) (initial_lo : nat) (hi : nat) {measure (hi-lo)} : (nat*list nat) :=
    match ((partition_left l pivot lo hi), (partition_right l pivot lo hi)) with
    | (i, j) => match j <=? i with
        | false => match (j <=? hi) with
            | true => match (lo <=? i) with 
                | true => partition (swap l i j) pivot (i+1) initial_lo (j-1)
                | false => (j,[]) (* will never happen *)
                end
            | false => (j,[]) (* will never happen *)
            end
        | true => (j, (swap l initial_lo j))
    end end.
Next Obligation.
(* symmetry in Heq_anonymous. apply leb_complete_conv in Heq_anonymous. assert (partition_right l pivot lo hi <= hi). apply partition_right_le. assert (partition_left l pivot lo hi >= lo). apply partition_left_ge.
apply helper. trivial. trivial. trivial. *)
symmetry in Heq_anonymous1. apply leb_complete_conv in Heq_anonymous1. symmetry in Heq_anonymous.
apply Nat.leb_le in Heq_anonymous. symmetry in Heq_anonymous2. apply Nat.leb_le in Heq_anonymous2. apply helper. trivial. trivial. trivial.
Qed.

Compute (partition (shuffle [15;14;13;12;11;10;5;2;6;3;1;4;9;8;7]) 12 0 0 14).

Program Fixpoint sort (l : list nat) (lo : nat) (hi : nat) {measure (hi-lo)} : list nat :=
    match (hi <=? lo) with
    | true => l
    | false => match (partition l (lookup l lo) lo lo hi) with
        | (j, partitioned) => match ((j <=? hi) && (lo <=? j)) with 
            | false => l (* will never happen *)
            | true => sort (sort partitioned lo (j-1)) (j+1) hi
            end
    end end.
Next Obligation.
symmetry in Heq_anonymous0. apply leb_complete_conv in Heq_anonymous0.
symmetry in Heq_anonymous. apply andb_true_iff in Heq_anonymous. destruct  Heq_anonymous.
apply Nat.leb_le in H.
lia.
Qed.
Next Obligation.
symmetry in Heq_anonymous0. apply leb_complete_conv in Heq_anonymous0.
symmetry in Heq_anonymous. apply andb_true_iff in Heq_anonymous. destruct  Heq_anonymous.
apply Nat.leb_le in H0.
lia.
Qed.

Program Fixpoint sort2 (l : list nat) (lo : nat) (hi : nat) (_:lo<=hi) {measure (hi-lo)} : list nat :=
    match (hi <=? lo) with
    | true => l
    | false => match (partition l (lookup l lo) lo lo hi) with
        | (j, partitioned) => match ((j <=? hi) && (lo <=? j)) with 
            | false => l (* will never happen *)
            | true => sort (sort partitioned lo (j-1)) (j+1) hi
            end
    end end.

Definition quicksort (l : list nat) : list nat :=
    match (shuffle l) with
    (* | shuffeled => shuffeled  *)
    | shuffled => sort shuffled 0 (List.length shuffled - 1)
    end.

Compute (quicksort [15;14;13;12;11;10;5;2;6;3;1;4;9;8;7]).
Compute (quicksort [66; 91; 69; 62; 52; 10; 49; 38; 53; 54; 98; 95; 92; 6; 20; 32; 41; 71; 59; 25; 80; 75; 73; 79; 63; 48; 12; 46; 28; 68; 65; 24; 81; 85; 47; 35; 33; 30; 17; 72; 7; 89; 40; 39; 94; 51; 13; 11; 67; 16; 76; 31; 77; 60; 82; 61; 42; 18; 36; 87; 93; 88; 26; 22; 8; 4; 84; 29; 21; 97; 56; 2; 37; 90; 9; 15; 50; 58; 70; 78; 19; 99; 86; 44; 96; 1; 100; 14; 43; 64; 55; 3; 27; 45; 74; 0; 23; 57; 34; 5; 83]).
Compute (quicksort [163; 924; 313; 374; 81; 679; 398; 785; 842; 408; 191; 60; 794; 216; 791; 749; 424; 661; 383; 898; 203; 405; 479; 620; 322; 451; 634; 72; 884; 20; 750; 925; 496; 542; 440; 284; 411; 698; 556; 154; 446; 674; 397; 716; 540; 441; 230; 551; 367; 183; 115; 643; 905; 178; 356; 660; 37; 636; 433; 387; 30; 63; 912; 276; 967; 965; 179; 910; 861; 426; 558; 66; 439; 263; 756; 489; 848; 903; 492; 992; 641; 597; 516; 310; 784; 456; 635; 327; 198; 854; 93; 278; 545; 6; 865; 533; 793; 318; 217; 614; 527; 249; 826; 880; 930; 735; 822; 612; 937; 258; 369; 24; 246; 658; 262; 891; 469; 510; 528; 195; 240; 990; 963; 388; 131; 882; 897; 53; 602; 889; 581; 772; 182; 59; 710; 427; 337; 366; 700; 351; 590; 873; 714; 82; 259; 639; 790; 22; 87; 52; 128; 202; 472; 977; 526; 270; 974; 904; 952; 333; 393; 942; 301; 729; 232; 565; 821; 675; 814; 940; 566; 838; 626; 563; 119; 702; 836; 438; 375; 519; 175; 778; 863; 35; 483; 521; 169; 697; 89; 399; 713; 999; 292; 423; 135; 642; 325; 382; 689; 224; 820; 680; 773; 458; 693; 461; 909; 613; 707; 272; 332; 338; 190; 657; 67; 293; 319; 960; 363; 831; 746; 801; 430; 271; 671; 158; 107; 464; 871; 979; 275; 127; 633; 616; 166; 984; 357; 417; 637; 650; 605; 941; 390; 104; 630; 391; 58; 122; 656; 985; 741; 568; 732; 260; 47; 969; 274; 269; 806; 864; 346; 171; 734; 421; 887; 347; 872; 678; 947; 100; 414; 499; 587; 447; 893; 416; 400; 384; 315; 829; 134; 381; 792; 890; 517; 490; 804; 847; 694; 686; 164; 449; 353; 913; 592; 55; 437; 757; 525; 788; 473; 603; 585; 95; 908; 948; 879; 782; 43; 976; 761; 205; 45; 121; 304; 255; 307; 481; 90; 582; 894; 453; 54; 500; 564; 345; 966; 401; 389; 34; 759; 724; 403; 751; 139; 50; 125; 931; 813; 736; 250; 508; 101; 611; 40; 218; 0; 340; 860; 409; 176; 599; 550; 277; 874; 254; 972; 619; 415; 537; 1; 684; 627; 144; 291; 442; 429; 522; 964; 797; 33; 225; 237; 448; 222; 951; 640; 359; 482; 8; 404; 392; 161; 719; 126; 209; 159; 877; 770; 557; 5; 49; 807; 955; 311; 850; 286; 596; 598; 186; 738; 799; 302; 844; 845; 800; 962; 852; 42; 601; 774; 594; 561; 544; 248; 803; 26; 257; 410; 470; 444; 380; 206; 112; 12; 339; 288; 975; 923; 364; 308; 497; 78; 71; 888; 494; 91; 204; 187; 267; 362; 926; 110; 3; 253; 840; 827; 130; 76; 744; 978; 487; 753; 685; 562; 192; 454; 932; 287; 628; 745; 303; 94; 712; 419; 652; 769; 378; 688; 120; 896; 450; 385; 938; 68; 109; 97; 867; 491; 858; 343; 928; 137; 535; 754; 504; 870; 810; 731; 560; 953; 939; 221; 553; 355; 728; 280; 79; 148; 23; 266; 866; 412; 593; 506; 48; 486; 715; 242; 235; 644; 312; 170; 869; 11; 503; 201; 523; 841; 816; 478; 342; 541; 907; 809; 708; 659; 775; 452; 915; 70; 629; 811; 65; 349; 372; 580; 62; 514; 878; 428; 569; 954; 25; 329; 690; 995; 354; 615; 309; 281; 959; 664; 748; 717; 997; 763; 767; 279; 958; 181; 406; 305; 740; 682; 762; 677; 911; 379; 243; 157; 624; 98; 189; 968; 971; 376; 579; 875; 306; 80; 160; 956; 648; 546; 548; 457; 950; 994; 723; 933; 771; 256; 849; 2; 57; 588; 881; 536; 733; 85; 837; 141; 808; 973; 666; 672; 998; 435; 921; 518; 229; 760; 207; 488; 777; 214; 103; 386; 434; 991; 725; 226; 764; 467; 402; 589; 862; 670; 117; 502; 335; 418; 145; 118; 818; 324; 577; 779; 236; 855; 283; 41; 920; 649; 895; 162; 511; 326; 625; 567; 621; 51; 505; 591; 9; 781; 106; 228; 252; 739; 239; 373; 632; 783; 654; 886; 321; 681; 73; 463; 696; 431; 857; 348; 663; 916; 213; 476; 946; 987; 297; 289; 299; 394; 151; 983; 687; 241; 509; 631; 282; 531; 856; 507; 173; 574; 196; 970; 554; 529; 147; 833; 140; 555; 828; 317; 74; 600; 919; 815; 92; 296; 669; 945; 233; 776; 922; 532; 31; 123; 432; 722; 84; 330; 993; 691; 798; 901; 165; 655; 193; 683; 231; 934; 264; 695; 651; 780; 552; 495; 943; 344; 906; 726; 543; 36; 727; 986; 843; 576; 718; 268; 210; 114; 835; 136; 573; 223; 455; 413; 957; 44; 586; 7; 61; 787; 19; 876; 200; 706; 96; 167; 102; 480; 766; 802; 138; 377; 133; 132; 320; 17; 445; 177; 371; 295; 16; 665; 667; 743; 352; 575; 350; 184; 980; 851; 28; 168; 617; 936; 512; 38; 834; 720; 825; 99; 111; 46; 647; 883; 420; 358; 524; 609; 116; 244; 900; 832; 595; 294; 234; 645; 174; 653; 699; 703; 853; 513; 323; 436; 668; 247; 468; 108; 578; 21; 988; 755; 570; 823; 752; 300; 290; 466; 64; 285; 341; 86; 227; 152; 742; 331; 215; 425; 142; 18; 129; 13; 29; 982; 944; 314; 251; 758; 56; 711; 395; 618; 14; 334; 819; 549; 39; 485; 949; 673; 113; 361; 32; 75; 459; 622; 462; 817; 149; 824; 830; 180; 530; 298; 515; 493; 676; 606; 892; 701; 839; 868; 4; 188; 199; 927; 328; 238; 150; 796; 273; 539; 460; 899; 805; 704; 501; 245; 859; 15; 172; 610; 407; 747; 989; 584; 981; 27; 422; 885; 812; 261; 156; 646; 559; 608; 197; 475; 692; 918; 105; 365; 88; 484; 185; 996; 623; 571; 370; 474; 360; 730; 538; 961; 194; 77; 662; 124; 572; 902; 789; 583; 69; 471; 10; 768; 607; 737; 153; 396; 265; 846; 211; 534; 336; 914; 604; 638; 465; 917; 547; 443; 709; 143; 795; 83; 498; 208; 765; 929; 316; 477; 220; 219; 146; 520; 786; 155; 935; 368; 721; 212; 705]).
Example quicksort_example1:
    quicksort [2;3;1;4] = [1;2;3;4].
Proof.
    reflexivity.
Qed.







(* Fixpoint partition (l : list nat) (lo : nat) (hi : nat) : list nat :=
    match l with
    | [] => l
    | [x] => l 
    | [h :: t] => 





Definition quicksort (l : list nat) : list nat :=
    shuffle l *)





type ('a, 'b) prod =
| Pair of 'a * 'b

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _::l' -> (fun x -> x + 1) (length l')

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h

(** val add : int -> int -> int **)

let rec add = ( + )

(** val mul : int -> int -> int **)

let rec mul = ( - )

(** val sub : int -> int -> int **)

let rec sub = ( - )

module Nat =
 struct
  (** val sub : int -> int -> int **)

  let rec sub n m =
    (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
      (fun _ -> n)
      (fun k ->
      (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
        (fun _ -> n)
        (fun l -> sub k l)
        m)
      n

  (** val divmod : int -> int -> int -> int -> (int, int) prod **)

  let rec divmod x y q u =
    (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
      (fun _ -> Pair (q, u))
      (fun x' ->
      (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
        (fun _ -> divmod x' y ((fun x -> x + 1) q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::t -> fold_left f t (f a0 b)

(** val lookup : int list -> int -> int **)

let rec lookup l i =
  match l with
  | [] -> 0
  | h::t -> if (<=) i 0 then h else lookup t (sub i ((fun x -> x + 1) 0))

(** val insert : int -> int -> int list -> int list **)

let rec insert elem index l =
  (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
    (fun _ -> match l with
              | [] -> elem::[]
              | _::xs -> elem::xs)
    (fun _ ->
    match l with
    | [] -> elem::[]
    | x::xs -> x::(insert elem (sub index ((fun x -> x + 1) 0)) xs))
    index

(** val randnat : int -> int -> int **)

let randnat seed bound =
  Nat.modulo
    (add
      (mul seed ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) 0)))))))))))))))))))))))))))))))) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) 0)))))))) bound

(** val fst3 : ((int list, int) prod, int) prod -> int list **)

let fst3 = function
| Pair (p, _) -> let Pair (a, _) = p in a

(** val swap : int list -> int -> int -> int list **)

let swap l i1 i2 =
  insert (lookup l i2) i1 (insert (lookup l i1) i2 l)

(** val shuffle : int list -> int list **)

let shuffle l =
  fst3
    (fold_left (fun acc _ ->
      let Pair (p, point) = acc in
      let Pair (li, seed) = p in
      Pair ((Pair ((swap li point (randnat seed (length li))), (add seed ((fun x -> x + 1) 0)))),
      (add point ((fun x -> x + 1) 0)))) l (Pair ((Pair (l, ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      0)))))))))))))))))))))))))))))))))))))))))))), 0)))

(** val partition_left_func : (int list, (int, (int, int) sigT) sigT) sigT -> int **)

let rec partition_left_func x =
  let l = projT1 x in
  let pivot = projT1 (projT2 x) in
  let lo = projT1 (projT2 (projT2 x)) in
  let hi = projT2 (projT2 (projT2 x)) in
  let partition_left0 = fun l0 pivot0 lo0 hi0 ->
    partition_left_func (ExistT (l0, (ExistT (pivot0, (ExistT (lo0, hi0))))))
  in
  let filtered_var = (<=) hi lo in
  if filtered_var
  then lo
  else let filtered_var0 = (<=) (lookup l lo) pivot in
       if filtered_var0 then partition_left0 l pivot (add lo ((fun x -> x + 1) 0)) hi else lo

(** val partition_left : int list -> int -> int -> int -> int **)

let partition_left l pivot lo hi =
  partition_left_func (ExistT (l, (ExistT (pivot, (ExistT (lo, hi))))))

(** val partition_right_func : (int list, (int, (int, int) sigT) sigT) sigT -> int **)

let rec partition_right_func x =
  let l = projT1 x in
  let pivot = projT1 (projT2 x) in
  let lo = projT1 (projT2 (projT2 x)) in
  let hi = projT2 (projT2 (projT2 x)) in
  let partition_right0 = fun l0 pivot0 lo0 hi0 ->
    partition_right_func (ExistT (l0, (ExistT (pivot0, (ExistT (lo0, hi0))))))
  in
  let filtered_var = (<=) hi lo in
  if filtered_var
  then hi
  else let filtered_var0 = (<=) pivot (lookup l hi) in
       if filtered_var0 then partition_right0 l pivot lo (sub hi ((fun x -> x + 1) 0)) else hi

(** val partition_right : int list -> int -> int -> int -> int **)

let partition_right l pivot lo hi =
  partition_right_func (ExistT (l, (ExistT (pivot, (ExistT (lo, hi))))))

(** val partition_func :
    (int list, (int, (int, (int, int) sigT) sigT) sigT) sigT -> (int, int list) prod **)

let rec partition_func x =
  let l = projT1 x in
  let pivot = projT1 (projT2 x) in
  let lo = projT1 (projT2 (projT2 x)) in
  let initial_lo = projT1 (projT2 (projT2 (projT2 x))) in
  let hi = projT2 (projT2 (projT2 (projT2 x))) in
  let partition0 = fun l0 pivot0 lo0 initial_lo0 hi0 ->
    partition_func (ExistT (l0, (ExistT (pivot0, (ExistT (lo0, (ExistT (initial_lo0, hi0))))))))
  in
  let filtered_var = Pair ((partition_left l pivot lo hi), (partition_right l pivot lo hi)) in
  let Pair (i, j) = filtered_var in
  let filtered_var0 = (<=) j i in
  if filtered_var0
  then Pair (j, (swap l initial_lo j))
  else let filtered_var1 = (<=) j hi in
       if filtered_var1
       then let filtered_var2 = (<=) lo i in
            if filtered_var2 then partition0 (swap l i j) pivot i initial_lo j else Pair (j, l)
       else Pair (j, l)

(** val partition : int list -> int -> int -> int -> int -> (int, int list) prod **)

let partition l pivot lo initial_lo hi =
  partition_func (ExistT (l, (ExistT (pivot, (ExistT (lo, (ExistT (initial_lo, hi))))))))

(** val sort_func : (int list, (int, int) sigT) sigT -> int list **)

let rec sort_func x =
  let l = projT1 x in
  let lo = projT1 (projT2 x) in
  let hi = projT2 (projT2 x) in
  let sort0 = fun l0 lo0 hi0 -> sort_func (ExistT (l0, (ExistT (lo0, hi0)))) in
  let filtered_var = (<=) hi lo in
  if filtered_var
  then l
  else let filtered_var0 = partition l (lookup l lo) lo lo hi in
       let Pair (j, partitioned) = filtered_var0 in
       let filtered_var1 = if (<=) j hi then (<=) lo j else false in
       if filtered_var1
       then sort0 (sort0 partitioned lo (sub j ((fun x -> x + 1) 0))) (add j ((fun x -> x + 1) 0))
              hi
       else []

(** val sort : int list -> int -> int -> int list **)

let sort l lo hi =
  sort_func (ExistT (l, (ExistT (lo, hi))))

(** val quicksort : int list -> int list **)

let quicksort l =
  let shuffled = shuffle l in sort shuffled 0 (sub (length shuffled) ((fun x -> x + 1) 0))

  let time f x =
    let t = Sys.time() in
    (* for i = 1 to 1000 do *)
    f x;
    (* done; *)
    Printf.printf "Execution time: %fs\n" (Sys.time() -. t);
;;

let list = [46; 36; 743; 854; 373; 457; 910; 977; 15; 532; 10; 488; 499; 599; 678; 48; 240; 310; 545; 140; 37; 58; 584; 528; 993; 984; 579; 951; 765; 516; 846; 54; 562; 776; 207; 320; 830; 415; 147; 907; 615; 241; 647; 61; 825; 366; 820; 794; 230; 730; 165; 557; 100; 231; 655; 815; 14; 495; 252; 564; 110; 885; 543; 385; 410; 660; 821; 858; 278; 498; 920; 896; 74; 573; 178; 133; 153; 426; 8; 200; 160; 803; 118; 130; 119; 566; 472; 664; 924; 242; 433; 672; 451; 295; 877; 411; 521; 158; 203; 435; 314; 778; 296; 365; 175; 214; 942; 473; 477; 96; 99; 705; 9; 400; 565; 603; 769; 325; 572; 41; 915; 236; 644; 487; 571; 66; 268; 206; 946; 801; 316; 525; 875; 195; 661; 70; 558; 595; 671; 479; 504; 93; 909; 962; 531; 802; 109; 880; 777; 873; 51; 856; 767; 356; 476; 317; 768; 760; 346; 281; 956; 224; 693; 82; 630; 334; 606; 925; 891; 945; 361; 271; 943; 374; 964; 982; 470; 492; 675; 31; 88; 652; 757; 600; 167; 125; 371; 699; 781; 399; 513; 221; 941; 506; 225; 233; 155; 35; 23; 306; 862; 640; 842; 916; 549; 185; 673; 326; 895; 98; 892; 388; 612; 45; 756; 646; 701; 779; 948; 827; 548; 975; 530; 774; 328; 949; 166; 204; 117; 855; 719; 450; 18; 616; 810; 376; 150; 822; 836; 406; 114; 838; 832; 351; 997; 196; 362; 255; 75; 986; 638; 403; 247; 370; 339; 834; 300; 398; 582; 868; 44; 429; 976; 16; 336; 805; 935; 859; 879; 750; 844; 392; 835; 265; 944; 81; 511; 246; 695; 849; 105; 355; 837; 145; 157; 170; 42; 340; 179; 734; 512; 83; 773; 539; 787; 733; 173; 890; 737; 619; 78; 688; 302; 736; 687; 439; 662; 276; 111; 929; 84; 186; 563; 223; 449; 629; 546; 799; 417; 874; 387; 354; 684; 823; 796; 394; 763; 104; 732; 707; 448; 65; 697; 138; 115; 953; 437; 894; 292; 724; 714; 632; 282; 494; 43; 464; 807; 508; 605; 193; 785; 995; 430; 454; 235; 55; 902; 288; 575; 650; 937; 791; 628; 409; 298; 496; 20; 639; 520; 524; 95; 27; 906; 76; 131; 708; 67; 980; 775; 134; 586; 501; 793; 839; 335; 419; 570; 38; 201; 79; 2; 610; 729; 715; 491; 792; 460; 940; 865; 1; 669; 884; 210; 71; 690; 139; 294; 913; 222; 350; 47; 445; 740; 227; 818; 478; 950; 262; 623; 305; 555; 635; 181; 50; 551; 280; 289; 342; 968; 552; 938; 621; 414; 63; 192; 367; 540; 245; 978; 515; 681; 624; 857; 989; 608; 788; 826; 816; 274; 591; 503; 840; 481; 213; 903; 299; 867; 259; 190; 369; 592; 659; 126; 853; 748; 412; 614; 955; 357; 798; 988; 208; 611; 696; 527; 625; 553; 852; 700; 263; 522; 904; 172; 363; 26; 665; 758; 250; 617; 483; 800; 284; 654; 323; 169; 359; 0; 954; 141; 452; 973; 596; 4; 979; 216; 722; 934; 237; 739; 686; 127; 927; 601; 163; 422; 795; 797; 550; 847; 62; 467; 922; 443; 103; 872; 59; 386; 189; 420; 576; 965; 560; 393; 446; 6; 958; 184; 123; 581; 742; 264; 761; 985; 128; 391; 279; 783; 931; 667; 970; 685; 755; 771; 692; 33; 542; 382; 709; 604; 547; 440; 731; 607; 122; 338; 21; 883; 538; 442; 510; 658; 329; 561; 290; 674; 833; 220; 923; 348; 112; 30; 497; 808; 741; 234; 270; 882; 5; 372; 718; 999; 912; 286; 384; 738; 649; 202; 991; 972; 971; 994; 142; 215; 68; 921; 514; 784; 421; 642; 747; 716; 998; 159; 593; 966; 983; 770; 277; 269; 13; 556; 380; 679; 156; 952; 753; 482; 466; 424; 469; 148; 967; 594; 187; 888; 651; 161; 529; 710; 926; 319; 580; 416; 212; 752; 405; 764; 444; 407; 368; 19; 56; 609; 211; 706; 260; 69; 726; 850; 106; 918; 364; 378; 887; 345; 254; 772; 897; 154; 25; 197; 267; 253; 641; 168; 397; 17; 588; 507; 453; 313; 199; 759; 465; 957; 861; 585; 413; 789; 898; 819; 643; 92; 914; 682; 817; 358; 341; 790; 273; 218; 653; 441; 137; 238; 303; 864; 301; 91; 7; 87; 786; 72; 782; 243; 804; 52; 132; 484; 377; 911; 493; 689; 80; 663; 704; 257; 828; 402; 401; 176; 749; 831; 694; 981; 102; 712; 90; 780; 554; 331; 57; 899; 389; 960; 304; 425; 474; 567; 275; 627; 992; 229; 349; 89; 930; 933; 353; 177; 459; 144; 171; 423; 152; 458; 297; 746; 135; 533; 841; 49; 698; 568; 597; 315; 182; 486; 266; 809; 535; 352; 77; 480; 932; 475; 396; 272; 908; 622; 293; 762; 332; 569; 447; 94; 309; 330; 226; 959; 97; 863; 613; 536; 228; 509; 744; 343; 53; 11; 893; 244; 468; 22; 24; 851; 285; 987; 333; 463; 146; 124; 754; 668; 814; 64; 205; 327; 860; 721; 936; 404; 871; 845; 219; 136; 947; 434; 73; 518; 745; 876; 634; 149; 251; 574; 598; 578; 324; 379; 209; 711; 287; 723; 232; 889; 431; 645; 107; 939; 248; 720; 824; 963; 677; 113; 505; 180; 151; 666; 121; 120; 517; 713; 905; 537; 523; 657; 239; 727; 85; 34; 101; 32; 418; 961; 900; 583; 544; 870; 878; 29; 432; 490; 347; 344; 217; 485; 848; 395; 198; 990; 108; 717; 680; 974; 587; 919; 589; 626; 869; 691; 751; 703; 360; 917; 321; 375; 670; 318; 28; 534; 129; 3; 308; 590; 648; 500; 337; 683; 261; 969; 620; 806; 843; 519; 183; 322; 813; 602; 456; 886; 471; 636; 428; 502; 462; 60; 526; 618; 291; 728; 381; 143; 637; 656; 577; 256; 436; 866; 427; 39; 40; 633; 12; 390; 702; 631; 188; 455; 408; 174; 461; 249; 311; 191; 86; 881; 312; 901; 811; 996; 116; 725; 194; 676; 307; 162; 283; 812; 383; 258; 541; 489; 164; 735; 829; 438; 559; 766; 928];;

time quicksort list
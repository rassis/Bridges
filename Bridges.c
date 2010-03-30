/* BRIDGES: Asymmetric search for strong local similarities. sequence1 is database - I create a look-up table for it. sequence2 is query - I am looking for its KS-words, and assemble them in chains, without detalization.
   Before this, KM-words that are too common in individual sequences are masked, in linear time.
   Sequences can be either naked or in FASTA format. There is only one database sequence, but there may be a list of queries in FASTA format, and each can be processed in both orientations. */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

static char ReadGoodChar   (FILE *);
static long Good           (char);
static char Comp           (char);
static long LetterToNumber (char);
static void RetrieveSeq    (FILE *, long, long, char *);
static char FileToSeq      (long, char);
static char SeqToPrint     (char);
static char UpperToLower   (char);
static char LowerToUpper   (char);
static long ReadFastA(FILE *, char *);
static void KMWordCover (long, long, long, char *, long *, unsigned char *);
static void Masking (long, long, long, long, long, long, long, long, long, long, long, unsigned char *, unsigned char *, long double (*)[4], long double (*)[4], char *);
static void MaskingLight (long, long, long, long, unsigned char *, long double (*)[4], char *seq);

int main(void)
{
  FILE *fseq1, *fseq2, *fseqM1, *fseqM2, *fout;
  long SeqL1Max, SeqL2Max, LastQuery = 0, LNameDB, LNameQ, NumQ, ori, L1, L2, j, k, l, m, m1, m2, KM4, KS4, *Arr4K, *List;
  long i, KM, InvComp, PostProcess, LowCase, FullMatrix, KS, FilterDBase, FilterQuery, FilterMode, FilterMatch, UnfilterDBase, UnfilterQuery, UnfilterMatch, FlatGap, MaxDist, MinWeight, MaxWordDB, MaxSimA, MaxSimF;
  long double E1, E2, P1[15][4], P2[15][4], Over1[10], Over2[10];
  float CoeffMis, CoeffGap, FractMaxOver, FractMinOver, CoeffMisPost;
  char c, *seq1, *seq2, NameDB[100], NameQ[100];
  unsigned char *MaskOne4K, *MaskTwo4K;
  long Condition, Lead, NWord, Mult, gap, mis, incr, mergeW, NSimF, NSimA, IndSim, dist1, dist2, NKWord, MaxOver, MinOver, CountOver1, CountOver2, MaxDistPost, PrintSeq;
  long LetFreq1[4], LetFreq2[4], LetNum[4], *Places, *TailP, *Tail, *TailL, *TailW, (*SimA)[5], (*SimF)[5];

/*   Parameters */
  char * inp1 =  "simChr4.fa.line"; char * inp2 = "simChr4.fa.line_copy";     /* Names of input files for database and for query) */
  SeqL1Max      =  125000000;    /* Maximal length of 1st sequence (database). The total memory requirement is maximum of 2*4**KM+L1+L2 and 4**(KS+1)+5*L1+L2 */
  SeqL2Max      =  125000000;    /* Maximal length of 2nd sequence (query). */
  MaxSimA       =      10000;    /* Maximal number of active similarities - internal */
  MaxSimF       =      10000;    /* Maximal number of finished similarities - internal */
  MaxWordDB     =      10000;    /* Maximal number of occurrences of KS word in the database sequence - internal */
  LowCase       =          0;    /* How to deal with lowercase letters: 0 - convert to uppercase, 1 - keep masked */ if (LowCase != 0 && LowCase != 1)                 { fprintf(fout, " Error: LowCase!"); goto quit; }
  InvComp       =          2;    /* Orientation of query sequence(s) 0 - direct, 1 - reverse, 2 - both */            if (InvComp != 0 && InvComp != 1 && InvComp != 2) { fprintf(fout, " Error: InvComp!"); goto quit; }
  FullMatrix    =          0;    /* Consider sub-diagonal half of matrix, including diagonal? 0 - no, 1 - yes */      if (FullMatrix != 0 && FullMatrix != 1)           { fprintf(fout, " Error: NoDaig!"); goto quit; }
  KM            =         14;    /* Length of K-words for masking, not too many words must be expected*/             if (KM < 3 || KM > 14)                            { fprintf(fout, " Error: KM!"); goto quit; }
  FilterDBase   =      10000;    /* Maximal allowed number of a KM word in sequence 1 - if more, filter */           if (FilterDBase < 3 || FilterDBase > 1000000000)  { fprintf(fout, " Error: FilterDBase!"); goto quit; }
  FilterQuery   =      10000;    /* Maximal allowed number of a KM word in sequence 2 - if more, filter */           if (FilterQuery < 3 || FilterQuery > 1000000)     { fprintf(fout, " Error: FilterQuery!"); goto quit; }
  KS            =         12;    /* Length of K-words for searching, the longer the faster and less sensitive */     if (KS < 3 || KS > 14)                            { fprintf(fout, " Error: KS!"); goto quit; }
  CoeffMis      =       0.01;    /* Penalty for a mismatch within the maximal possible block of mismatches */        if (CoeffMis < 0.0 || CoeffMis > 10.0)            { fprintf(fout, " Error: CoeffMis!"); goto quit; }
  CoeffGap      =       0.05;    /* Elongation penalty for the minimal possible gap */                               if (CoeffGap < 0.0 || CoeffGap > 10.0)            { fprintf(fout, " Error: CoeffGap!"); goto quit; }
  FlatGap       =         10;    /* Gap length after which the penalty does not increase */                          if (FlatGap  < 1 || FlatGap > 100)                { fprintf(fout, " Error: FlatGap!"); goto quit; }
  MaxDist       =        100;    /* Maximal distance, in ether sequence, between K-words that form a chain */        if (MaxDist  < 1 || MaxDist > 10000)              { fprintf(fout, " Error: MaxDist!"); goto quit; }
  MinWeight     =        500;    /* Minimal weight of an important local similarity */                               if (MinWeight < 1 || MinWeight > 100000)          { fprintf(fout, " Error: MinWeight!"); goto quit; }
  PostProcess   =          1;    /* Post-process found chains of matches? 0 - no, 1 - yes */                          if (PostProcess < 0 || PostProcess > 1)           { fprintf(fout, " Error: PostProcess!"); goto quit; }
  MaxOver       =        100;    /* Maximal coverage, of either sequence, allowed under a similarity */              if (MaxOver < 1 || MaxOver > 255)                 { fprintf(fout, " Error: MaxOver!"); goto quit; }
  MinOver       =          2;    /* Minimal coverage, of either sequence, allowed under a similarity */              if (MinOver < 1 || MinOver > 255)                 { fprintf(fout, " Error: MinOver!"); goto quit; }
  FractMaxOver  =        0.5;    /* Mask if the fraction of similarity over maximal coverage exceeds this value */    if (FractMaxOver < 0.0 || FractMaxOver > 1.0)     { fprintf(fout, " Error: FractMaxOver!"); goto quit; }
  FractMinOver  =        0.5;    /* Mask if the fraction of similarity over minimal coverage exceeds this value */    if (FractMinOver < 0.0 || FractMinOver > 1.0)     { fprintf(fout, " Error: FractMinOver!"); goto quit; }
  MaxDistPost   =       1000;    /* Maximal distance between the 1st-order chains that merge */                      if (MaxDistPost < 0 || MaxDistPost > 100000000)   { fprintf(fout, " Error: MaxDistPost!"); goto quit; }
  CoeffMisPost  =        0.1;    /* A coefficient with which "mismatches" are counted towards MaxDistPost */         if (CoeffMisPost < 0.0 || CoeffMisPost > 1.0)     { fprintf(fout, " Error: CoeffMisPost!"); goto quit; }
  PrintSeq      =          1;    /* Print sequences of the regions found? 0 - no, 1 - yes */                         if (PrintSeq < 0 || PrintSeq > 1)                 { fprintf(fout, " Error: PrintSeq!"); goto quit; }

  if ((fout  = fopen("Bridges.out","w")) == NULL) { fprintf(fout," no outfile "); goto quit; }                    /* Obvious things */
  fprintf(fout,"  LowCase = %2li  InvComp = %3li  FullMatrix = %2li\n", LowCase, InvComp, FullMatrix);
  fprintf(fout,"  KM = %3li  FilterDBase = %4li  FilterQuery = %4li  FilterMode = %4li\n", KM, FilterDBase, FilterQuery, FilterMode);
  fprintf(fout,"  KS = %3li  CoeffMis = %6.4f  CoeffGap = %6.4f  FlatGap = %3li  MaxDist = %4li  MinWeight = %6li  PostProcess = %2li\n", KS, CoeffMis, CoeffGap, FlatGap, MaxDist, MinWeight, PostProcess);
  if (PostProcess == 1)
    fprintf(fout," MaxOver = %3li  MinOver = %3li  FractMaxOver = %6.4f  FractMinOver = %6.4f  CoeffMisPost = %6.4f  MaxDistPost = %7li\n", MaxOver, MinOver, FractMaxOver, FractMinOver, CoeffMisPost, MaxDistPost);

  KM4 = 1; for (i = 0; i != KM; i ++) KM4 *= 4;                                                                   /* Power for longs */
  KS4 = 1; for (i = 0; i != KS; i ++) KS4 *= 4;                                                                   /* Power for longs */
  if ((seq1   = calloc(SeqL1Max, sizeof(char))) == NULL)  { fprintf(fout," No memory for seq1!   "); goto quit; } /* Memory allocation for database sequence */
  if ((seq2   = calloc(SeqL2Max, sizeof(char))) == NULL)  { fprintf(fout," No memory for seq2!   "); goto quit; } /* Memory allocation for query sequence(s) */
  if ((Places = calloc(MaxWordDB, sizeof(long))) == NULL) { fprintf(fout," No memory for Places! "); goto quit; } /* Unpacked locations of a KS word in the database (sequence 1) */
  if ((TailP  = calloc(MaxWordDB, sizeof(long))) == NULL) { fprintf(fout," No memory for TailP!  "); goto quit; } /* Potential attachments of tails to heads */
  if ((Tail   = calloc(MaxWordDB, sizeof(long))) == NULL) { fprintf(fout," No memory for Tail!   "); goto quit; } /* Potential attachments of tails to heads */
  if ((TailL  = calloc(MaxWordDB, sizeof(long))) == NULL) { fprintf(fout," No memory for TailL!  "); goto quit; } /* Potential attachments of tails to heads */
  if ((TailW  = calloc(MaxWordDB, sizeof(long))) == NULL) { fprintf(fout," No memory for TailW!  "); goto quit; } /* Weights of chains with different tails */
  if ((SimA   = calloc(MaxSimA*5, sizeof(long))) == NULL) { fprintf(fout," No memory for SimA!   "); goto quit; } /* List of active similarities, that still can be updated */
  if ((SimF   = calloc(MaxSimF*5, sizeof(long))) == NULL) { fprintf(fout," No memory for SimF!   "); goto quit; } /* List of active similarities, that still can be updated */
  if ((fseq1 = fopen(inp1,"r")) == NULL) { fprintf(fout," No database sequence! "); goto quit; }                  /* Opening input file containing database sequence */
  if ((fseq2 = fopen(inp2,"r")) == NULL) { fprintf(fout," No query sequence(s)! "); goto quit; }                  /* Opening input file containing query sequence(s) */

/*   Reading the only database sequence from input file */
  c = getc(fseq1);                                                                               /* The first character determines format of the database - FASTA or naked */
  if (c == '>') LNameDB = ReadFastA(fseq1,NameDB);                                               /* If database sequence is in FASTA format, get its name */
  else { LNameDB = 0; ungetc(c, fseq1); }                                                        /* Otherwise, database sequence will be unnamed */
  for (L1 = 0; ; L1 ++)                                                                          /* Reading database sequence - numbers, blanks, tabs and, newline characters are skipped */
  {
    c = ReadGoodChar(fseq1); if (c == EOF) break;                                                /* There is no special end_of_sequence symbol */
    if (c == '>') { fprintf(fout," Only one database sequence can be used! "); goto quit; }      /* Do not want to see another '>', but there is no control for other bad symbols */
    seq1[L1] = FileToSeq(LowCase,c);                                                             /* Converting lowercase letters either to uppercase or to internal symbols */
    if (L1 == SeqL1Max) break;                                                                   /* The database sequence is too long */
  }
  if (L1 < KS || L1 == SeqL1Max) { fprintf(fout, " Error: L1 = %10Li ", L1); goto quit; }         /* Do not process a sequence that are too short or too long */
  fclose(fseq1);                                                                                 /* This file will not be used below */
  if (LNameDB == 0) fprintf(fout,"\n     Database unnamed of length %10Li\n", L1);               /* Printing in case of naked database sequence or if there was no name in FASTA format */
  else                                                                                           /* Printing if the name of database sequence was provided */
  {
    fprintf(fout,"\n     Database ");
    for (i = 0; i != LNameDB; i ++) fprintf(fout,"%c", NameDB[i]);
    fprintf(fout," of length %10Li\n", L1);
  }

/*   Filtering the database - only KM word occurrences in the filtered sequence are counted, so that database can be filtered only once */
    if ((MaskOne4K = calloc(KM4, sizeof(unsigned char))) == NULL)                                /* Memory allocation for fast-masking database sequence - this huge array is freed after masking, to save memory */
       { fprintf(fout," No memory for MaskOne4K! "); goto quit; }
    KMWordCover(KM, KM4, L1, seq1, LetFreq1, MaskOne4K);                                         /* Recording occurrences of KM-words and nucleotide composition of database sequence */
    for (k = 0; k != 4; k ++) if (LetFreq1[k] == 0) LetFreq1[k] = 1;                             /* To deal with an impossible situation of an absent letter */
    for (m = 0; m != KM; m ++) for (k = 0; k != 4; k ++)                                         /* Pre-computing powers of frequencies, to speed up calculations below */
      P1[m][k] = pow(LetFreq1[k]/(long double)L1,m);
    MaskingLight(KM, KM4, L1, FilterDBase, MaskOne4K, P1, seq1);                                 /* Fast-masking database sequence */
    free(MaskOne4K);                                                                             /* Release the memory storing a huge array */

    m1 = 0; for (i = 0; i != L1; i++) if (Good(seq1[i]) == 0) m1 ++;                             /* Reporting the fraction of database sequence that was masked */
    fprintf (fout, " fraction of seq1 masked %f\n", (double)m1/L1);

    if ((fseqM1 = fopen("seq1M.txt","w")) == NULL) { fprintf(fout," no seq1M-1 " ); goto quit; } /* Storing fast-masked database sequence in internal file */
    for (i = 0; i != L1; i++) fprintf (fseqM1, "%c", seq1[i]);
    fclose(fseqM1);

for (NumQ = 0; ; NumQ ++)                                                                        /* Loop by query sequences - I do not know their number in advance */
{
/*   Reading a query sequence from input file */
  c = getc(fseq2);                                                                               /* The first character determines format of the current query - FASTA or naked. Multiple queries must be in FASTA format. */
  if (c == '>') LNameQ = ReadFastA(fseq2,NameQ);                                                 /* If query sequence(s) is in FASTA format, get its name(s) */
  else { LNameQ = 0; ungetc(c, fseq2); }                                                         /* Otherwise, query sequence(s) will be unnamed */
  for (L2 = 0; ; L2 ++)                                                                          /* Reading query sequence - numbers, blanks, tabs, and newline characters are skipped */
  {
    c = ReadGoodChar(fseq2); if (c == EOF)  { LastQuery = 1; break; }                            /* Even if the query is the last one, it sill needs to be processed */
    if ( c == '>' ) { ungetc(c, fseq2); break; }                                                 /* The 1st symbol in the FASTA line of the next query is reached */
    seq2[L2] = FileToSeq(LowCase,c);                                                             /* Converting lowercase letters either to uppercase or to internal symbols */
    if (L2 == SeqL2Max) break;                                                                   /* The query sequence is too long */
  }
  if (L2 < KS || L2 == SeqL2Max) { fprintf(fout, " Error: L2 = %10Li ", L2); goto quit; }         /* Do not process a sequence that are too short or too long */
  if (L2 < L1/10 && FullMatrix == 0) { fprintf(fout, " Error: diagonal ", L2); goto quit; }       /* To prevent confusions - when a query is short, everything happens below the diagonal */
  if (LNameQ == 0)                                                                               /* Printing in case of naked query sequence or if there was no name in FASTA format */
    fprintf(fout,"\n\n   Query number %5li, unnamed of length %10Li\n", NumQ+1, L2);
  else                                                                                           /* Printing if the name of query sequence was provided */
  {
    fprintf(fout,"\n\n   Query %5li, ", NumQ+1);
    for (i = 0; i != LNameQ; i ++) fprintf(fout,"%c", NameQ[i]);
    fprintf(fout," of length %10Li\n", L2);
  }

for (ori = 0; ori != 2; ori ++)                                                                  /* Loop by orientation of query sequence(s) */
{                                                                                                /* for (i = 0; i != KM4; i++)  fprintf(fout,"%5li\n", MaskOne4K[i]); */
  if (InvComp == 0 && ori == 1) continue; if (InvComp == 1 && ori == 0) continue;                /* Work only with the desired orientations */
  if (ori == 1)
  {
    if ((fseqM2 = fopen("seq2M.txt","r")) == NULL) { fprintf(fout," no seq2M-1 "); goto quit; }  /* Retrieving query sequence with invert-complementing */
    RetrieveSeq(fseqM2,L2,1,seq2);
    fclose(fseqM2);
  }

/*   Masking repetitive segments of the current query */
  if ((MaskTwo4K = calloc(KM4, sizeof(unsigned char))) == NULL)                                  /* Memory allocation for masking query sequence(s) - this huge array is freed after masking, to save memory */
     { fprintf(fout," No memory for MaskTwo4K! "); goto quit; }
  KMWordCover(KM, KM4, L2, seq2, LetFreq2, MaskTwo4K);                                           /* Recording occurrences of KM-words and nucleotide composition of query sequence(s) */
  for (k = 0; k != 4; k ++) if (LetFreq2[k] == 0) LetFreq2[k] = 1;                               /* To deal with an impossible situation of an absent letter */
  for (m = 0; m != KM; m ++) for (k = 0; k != 4; k ++)                                           /* Pre-computing powers of frequencies, to speed up calculations below */
    P2[m][k] = pow(LetFreq2[k]/(long double)L2,m);
  MaskingLight(KM, KM4, L2, FilterQuery, MaskTwo4K, P2, seq2);                                   /* Fast-masking query */
  free(MaskTwo4K);                                                                               /* Release the memory storing two huge arrays */

  if ((fseqM2 = fopen("seq2M.txt","w")) == NULL) { fprintf(fout," no seq2M-2 " ); goto quit; }   /* Storing masked query sequence in internal file */
  for (i = 0; i != L2; i++) fprintf (fseqM2, "%c", seq2[i]); fclose(fseqM2);
  m2 = 0; for (i = 0; i != L2; i++) if (Good(seq2[i]) == 0) m2 ++;                               /* Determining the fraction of query sequence that was masked */
  fprintf (fout, "\n  orientation %1li, fraction of seq2 masked %f\n", ori, (double)m2/L2);      /* Reporting the results */

/*   END_OF_MASKING, BEGINNING_OF_SEARCHING */

/* Search consists of screening the query sequence2, unpacking all occurrences of the observed KS words in sequence1, treating them as tails, and and attaching them to already-existig heads of growing chains of KS words */
  if ((Arr4K     = calloc(KS4,       sizeof(long))) == NULL) { fprintf(fout," No memory for Arr4K!  "); goto quit; } /* Arr4K is indexed by lexicographic numbers of all KS-words and contains references to the positions of their first occurrence in List */
  if ((List      = calloc(L1,        sizeof(long))) == NULL) { fprintf(fout," No memory for List!   "); goto quit; } /* List is indexed by positions and contains position of the data on the next occurrence of the KS-word */
  for (i = 0; i != KS4; i ++) Arr4K[i] = -1;                    /* 0 is a legitimate possibility for a content of this array */

/*   Preliminary work - Filling the look-up table for KS-words in sequence1, the database */
  Lead = 0; NWord = 0;                                          /* Initialization for accumulating the lexicographical number NWord of a KS word */
  for (i = 0; i != L1; i++)                                     /* Scan the sequence */
  {
	if (Good(seq1[i]) == 0) { Lead = 0; NWord = 0; }            /* If a letter is bad (not A, T, G, or C), reinitialize */
	else                                                        /* If a letter is good */
	{
	  Mult = LetterToNumber(seq1[i]);                           /* Take its number */
	  if (Lead < KS) NWord = NWord*4+Mult;                      /* Calculate NWord of an incomplete KS word */
	  else NWord = 4*(NWord % (KS4/4)) + Mult;                  /* Calculate NWord of a complete KS word - apparently, all this works correctly! */
	  Lead ++;                                                  /* Increment the counter of KS word completeness */
	}
	if (Lead >= KS)                                             /* Process only complete KS words */
	{
	  if (Arr4K[NWord] == -1) Arr4K[NWord] = i-KS+1;            /* Process the first occurrence of this KS-word - mark its start */
	  else                                                      /* Process a non-first occurrence of this KS-word */
   	  {
	    l = Arr4K[NWord];                                       /* Entering List through Arr4K interface */
	    for (m = 0; ; m++)
	    {
	      if (List[l] == 0) { List[l] = i-KS+1; break; }        /* Write the reference to the active position */
          l = List[l];
	    }
	  }
	}
  }

/*   Actual work - scanning sequence2 - query, looking for KS-words, and assembling their chains. A chain is assembled starting from its Head, which points left-down. We hold chains by their tails! */
  NSimF = NSimA = 0;                                            /* Initially, there are no finished similarities, and no active similarities */
  Lead = 0; NWord = 0;                                          /* Initialization for accumulating the lexicographical number NWord of a KS word */
  for (i = 0; i != L2; i++)                                     /* MAIN LOOP - scanning sequence2 - query */
  {
  	NKWord = 0;                                                 /* In case there will be no occurrences of the K-word */
	if (Good(seq2[i]) == 0) { Lead = 0; NWord = 0; }            /* If a letter is bad (not A, T, G, or C), reinitialize */
	else                                                        /* If a letter is good */
	{
	  Mult = LetterToNumber(seq2[i]);                           /* Take its number */
	  if (Lead < KS) NWord = NWord*4+Mult;                      /* Calculate NWord of an incomplete KS word */
	  else NWord = 4*(NWord % (KS4/4)) + Mult;                  /* Calculate NWord of a complete KS word */
	  Lead ++;                                                  /* Increment the counter of KS word completeness */
	}
    if (Lead < KS) goto noword;                                 /* If the KS-word contained bad symbols, ignore it */
    m = i - KS + 1;                                             /* To work in the same way with both sequences: Places holds the locations of the beginnings of KS-words in sequence1 (see how List is filled above), and m does the same for sequence2 */

/*   Unpack positions of this KS-word in seq1 into array Places */
    if (Arr4K[NWord] == -1) goto noword;                        /* If the K-word never occurred in sequence1, ignore it */
    l = Arr4K[NWord];                                           /* Extract information about a K-word that is present from the front array */
	Places[0] = l;                                              /* The position of the 1st occurrence of the K-word in seq1 */
	for (NKWord = 1; ; NKWord++)                                /* Looking for the subsequent positions of the same K-word */
	{
	  if (NKWord == MaxWordDB)
	    { fprintf(fout, " Error: MaxWordDB! "); goto quit; }     /* Did I allocate enough memory for temporary buffer Places? */
	  if (List[l] == 0) break;                                  /* If the last position is reached, record the number of words present */
	  l = List[l];                                              /* Next position */
	  Places[NKWord] = l;                                       /* Recording it */
	}

/*   Process new Tails - NKWord occurrences in sequence1 of the KS-word that is current in sequence2 */
    k = 0;
	for (l = 0; l != NKWord; l++)                               /* Loop by all new tails */
	{
	  if (FullMatrix == 0 && Places[l] >= m) continue;          /* Ignore the sub-diagonal part of the dot-matrix, including diagonal, if required */
   	  for (IndSim = 0; IndSim != NSimA; IndSim ++)              /* Scan all new Tails and weed out all those who are just continuation of active Heads - this is possible, because I try to extend each KS-word rightward */
      {
		dist1 = Places[l] - SimA[IndSim][1] - 1;                /* Distance between the beginning of a Tail and the end of a Head, in sequence1 */
        dist2 = m - SimA[IndSim][3] - 1;                        /* Distance between the beginning of a Tail and the end of a Head, in sequence2 */
		if (dist1 < 0 && dist1 == dist2)                        /* This Tail is just a continuation of a Head, so ignore it. Both distances cannot be equal to zero. */
        goto nexttail;
	  }
	  TailP[k] = Places[l];                                     /* Position of a good Tail */
	  Tail[k] = -1;                                             /* All new Tails are initially unattached to Heads (active similarities) */
      TailL[k] = KS;                                            /* Initially, all new Tails are KS matches long - they are just matches of KS-words */
      m1 = TailP[k]+KS-1; m2 = m+KS-1;                          /* Initializations for possible Tail extension - pointers to the last letters within the Tail in the two sequences */
      for (;;)                                                  /* Could this Tail be extended right-top-ward? */
	  {
	    m1++; m2++;                                             /* Increment pointers */
	    if (m1 == L1 || m2 == L2) break;                        /* If the end of a sequence is reached, stop extending */
	    if (Good(seq1[m1]) == 0 || Good(seq2[m2]) == 0) break;  /* If a bad symbol is encountered, stop extending */
	    if (seq1[m1] != seq2[m2]) break;                        /* If a mismatch is encountered, stop extending */
		TailL[k] ++;                                            /* Extend - it helps to deal with building blocks that have been extended right-up for as long as possible */
	  }
	  k ++;                                                     /* Incrementing the index of good Tails */
nexttail: ;                                                     /* The provisional Tail was bad */
	}
	NKWord = k;                                                 /* The number of good Tails which are not continuations */

/*   For each new Tail, merge it with the most suitable Head (active similarity) or create a new one */
	for (IndSim = 0; IndSim != NSimA; IndSim ++)                /* Scan all Heads, and for each Head find the new Tail it wants to acquire. Doing it in the opposite way - seeking the best Head for each Tail - is bad */
    {
	  dist2 = m - SimA[IndSim][3] - 1;                          /* Distance between the beginning of any Tail and the end of the Head, in sequence2 */
      if (dist2 < 0) continue;                                  /* Overlap along the Y axis is fatal: This Head was expanded past the location of beginnings of current Tails, so the Head consumed one of them and will not merge with any other */
	  for (l = 0; l != NKWord; l++)                             /* Scan all Tails */
	  {
	    dist1 = TailP[l] - SimA[IndSim][1] - 1;                 /* Distance between the beginning of a Tail and the end of a Head, in sequence1 */
	    if (dist1 > MaxDist) break;                             /* Potential Tails in sequence1 are ordered, so the next one would be even more distant */
        if (dist2 > MaxDist)
		{ fprintf(fout, " Error: Impossible! "); goto quit; }    /* Distance in sequence2 cannot be too large - unpromising similarities have just being removed from the list */
		if (dist1 < 0)                                          /* Overlap along the X axis is not necessarily fatal: just truncate the beginning of the Tail */
        {
		   incr = TailL[l] + dist1;                             /* How long is the end of Tail that can be merged with the Head? */
		   if (incr < KS) continue;                             /* If not enough of the Tail is to the right of the Head abandon this Tail */
		   gap = dist2 - dist1;                                 /* gap is the updated distance2, after the incompatible beginning of the Tail is truncated */
		   if (gap > MaxDist) continue;                         /* If the updated distance2 is too large, abandon this Tail */
		   if (gap > FlatGap) gap = FlatGap;                    /* Increment of the  weight of the Head, due to possible acquisition of the Tail */
           incr = incr - gap*CoeffGap;
		}
        else                                                    /* A "usual" situation - no overlap between the Head and the Tail it will acquire */
		{
		  if (dist1 >= dist2)                                   /* Calculating the maximal number of mismatches and the minimal overall length of gaps, consistent with dist1 and dist2 */
		    { gap = dist1 - dist2; mis = dist2; }               /* This is the most optimistic view, assuming that mismatches are penalized less than gaps */
	      else
		    { gap = dist2 - dist1; mis = dist1; }
		  if (gap > FlatGap) gap = FlatGap;                     /* Effective gap length, after truncation */
		  incr = TailL[l] - gap*CoeffGap - mis*CoeffMis;        /* Increment of the  weight of the Head, due to possible acquisition of the Tail */
		}
		if (incr <= 0) continue;                                /* Attaching Tail to Head is not a good idea */
		mergeW = SimA[IndSim][4]+incr;                          /* Weight of the similarity which will emerge if we implement this merge */
		if (Tail[l] != -1)                                      /* Tail under consideration for a Head already has another Head */
		{
		  if (mergeW <= TailW[l])                               /* Current Head wants Tail that is already a part of a chain that is not worse than the one that can be produced now */
		    { SimA[IndSim][4] = -1; break; }                    /* Kill the current Head, do nothing else */
		  SimA[Tail[l]][4] = -1;                                /* Head already attached to Tail produced weaker similarity than the one that can be produced now, kill the already attached Head  */
		}
		Tail[l] = IndSim;                                       /* New Head for the Tail */
		TailW[l] = mergeW;                                      /* Weight of a similarity which will appear if we attach the IndSim-th Head to the l-th Tail */
	  }
	}

/*   Updating the list of active similarities - updating Heads that acquired new Tails, and adding those consisting of new Tails alone */
noword: ;
    for (l = 0; l != NKWord; l++)                               /* Scanning all Tails */
	{
	  if (Tail[l] == -2) break;
	  if (Tail[l] != -1)			                            /* Tail became attached, so update the expanding Head */
	  {
		SimA[Tail[l]][1] = TailP[l]+TailL[l]-1;                 /* end of updated similarity in database */
		SimA[Tail[l]][3] = m+TailL[l]-1;                        /* end of updated similarity in query */
		SimA[Tail[l]][4] = TailW[l];                            /* weight of updated similarity */
	  }
	  else									                    /* Tail did not become attached, create a new chain from it */
	  {
		SimA[NSimA][0] = TailP[l];                              /* Beginning of similarity in database */
		SimA[NSimA][1] = TailP[l]+TailL[l]-1;                   /* End of similarity in database */
		SimA[NSimA][2] = m;                                     /* Beginning of similarity in query */
		SimA[NSimA][3] = m+TailL[l]-1;                          /* End of similarity in query */
		SimA[NSimA][4] = TailL[l];                              /* Weight of similarity */
		NSimA ++;                                               /* The number of active similarities increased by 1 */
		if (NSimA == MaxSimA) { fprintf (fout, " Error: MaxSimA!"); goto quit; }   /* Make sure the list of active similarities is not too large - if it grows out of control, performance will suffer */
 	  }
	}

/*   Scanning the list of active similarities for those marked for destruction and for those who will newer acquire new Tails - there is no need to scan those just updated or added, but this is not a big deal */
    for (IndSim = NSimA-1; IndSim != -1; IndSim --)                                    /* List of active similarities should be cleaned at each step in the main loop, as it is used as a whole */
    {
	  if (SimA[IndSim][4] != -1 && i - SimA[IndSim][3] < MaxDist) continue;            /* Live, promising similarity - do nothing - and all other similarities will be removed, perhaps after being printed */
	  if (SimA[IndSim][4] >= MinWeight && i - SimA[IndSim][3] >= MaxDist)              /* Live, non-promising, strong similarity - record it */
	  {
        for (k = 0; k != 5; k ++) SimF[NSimF][k] = SimA[IndSim][k];                    /* Recording a similarity into list of finished similarities */
		NSimF ++;                                                                      /* Incrementing the number of finished similarities */
        if (NSimF == MaxSimF) { fprintf (fout, " Error: MaxSimF!"); goto quit; }        /* Too many finished similarities */
	  }
      if (IndSim == NSimA - 1) NSimA --;                                               /* If the similarity to be removed from the active list is the last one, just decrement NSimA; */
	  else                                                                             /* Otherwise, replace a removed similarity with the last one from the list - this makes the list of similarities unordered */
	  {
	    for (k = 0; k != 5; k ++) SimA[IndSim][k] = SimA[NSimA-1][k];                  /* Replacing with the last one from the list */
		NSimA --;                                                                      /* Decrementing the number of similarities */
	  }
	}
  }  /* END_OF_MAIN_LOOP */

/*   Processing what is left - scan the array of active similarities; record strong ones */
  for (IndSim = 0; IndSim != NSimA; IndSim ++)                                         /* Loop by active similarities */
  {
    if (SimA[IndSim][4] >= MinWeight)                                                  /* Record a strong enough similarity */
	{
      for (k = 0; k != 5; k ++) SimF[NSimF][k] = SimA[IndSim][k];
	  NSimF ++;
      if (NSimF == MaxSimF) { fprintf (fout, " Error: MaxSimF!"); goto quit; }          /* Too many finished similarities */
	}
  }
  free(Arr4K); free(List);                                                             /* Release the memory storing two huge arrays */

  if (NSimF == 0) { fprintf (fout, "No similarities\n"); continue; }                   /* If there are no finished similarities, proceed to the next orientation/query */

/*   Simple post-processing of the list of found similarities, if desired */
  if (PostProcess == 1)                                                                /* Post-process or not? */
  {
/*     First stage of post-processing - removing similarities that correspond to segments that participate in too many and/or too few similarities */
    for (i = 0; i != L1; i ++) seq1[i] = 0;                                                           /* Calculating coverages of database and query - using sequences arrays, to save space */
    for (i = 0; i != L2; i ++) seq2[i] = 0;
    for (IndSim = 0; IndSim != NSimF; IndSim ++)
    {
      for (i = SimF[IndSim][0]; i != SimF[IndSim][1]+1; i ++) if (seq1[i] < 127) seq1[i] ++;
      for (i = SimF[IndSim][2]; i != SimF[IndSim][3]+1; i ++) if (seq2[i] < 127) seq2[i] ++;
    }
    for (k = 0; k != 10; k ++) { Over1[k] = Over2[k] = 0.0; }                                         /* Recording and reporting coverages */
	for (i = 0; i != L1; i ++) { k = seq1[i]; if (k > 9) k = 9; Over1[k] ++; }
    for (i = 0; i != L2; i ++) { k = seq2[i]; if (k > 9) k = 9; Over2[k] ++; }
    fprintf(fout," Coverages of the two sequences\n");
    for (k = 0; k != 10; k ++) { fprintf(fout," %f", (double)(Over1[k] /= L1)); } fprintf(fout,"\n");
    for (k = 0; k != 10; k ++) { fprintf(fout," %f", (double)(Over2[k] /= L2)); } fprintf(fout,"\n\n");

    for (IndSim = 0; IndSim != NSimF; IndSim ++)                                                      /* Killing similarities that overlap too much */
    {
      CountOver1 = CountOver2 = 0;
      for (i = SimF[IndSim][0]; i != SimF[IndSim][1]+1; i ++) if (seq1[i] > MaxOver) CountOver1 ++;
      for (i = SimF[IndSim][2]; i != SimF[IndSim][3]+1; i ++) if (seq2[i] > MaxOver) CountOver2 ++;
      if (CountOver1 > (SimF[IndSim][1]-SimF[IndSim][0])*FractMaxOver || CountOver2 > (SimF[IndSim][3]-SimF[IndSim][2])*FractMaxOver)
         SimF[IndSim][4] = -1;
    }

    for (IndSim = 0; IndSim != NSimF; IndSim ++)                                                      /* Killing similarities that overlap too little */
    {
      if (SimF[IndSim][4] == -1) continue;
      CountOver1 = CountOver2 = 0;
      for (i = SimF[IndSim][0]; i != SimF[IndSim][1]+1; i ++) if (seq1[i] < MinOver) CountOver1 ++;
      for (i = SimF[IndSim][2]; i != SimF[IndSim][3]+1; i ++) if (seq2[i] < MinOver) CountOver2 ++;
      if (CountOver1 > (SimF[IndSim][1]-SimF[IndSim][0])*FractMinOver || CountOver2 > (SimF[IndSim][3]-SimF[IndSim][2])*FractMinOver)
         SimF[IndSim][4] = -1;
    }

/*     Removing dead elements from the array of similarities, without reordering it */
    for (IndSim = 0; IndSim != NSimF; IndSim ++)                                            /* Finding the 1st dead element */
      if (SimF[IndSim][4] == -1) goto firstdead;                                            /* Here it is! */
    goto allgut;                                                                            /* No dead elements */
firstdead: ;                                                                                /* Processing the 1st dead element */
    if (IndSim == NSimF-1) goto allgut;                                                     /* The first dead element is the last one */
    else                                                                                    /* The first dead element is not the last one */
    {
      l = IndSim+1;                                                                         /* l - from where to start looking for the 1st non-dead element */
      for (;;)                                                                              /* Replacing a dead element */
      {
        for (i = l; i != NSimF; i ++)                                                       /* Looking for the next living element that follows the dead one */
          if (SimF[i][4] != -1) goto living;                                                /* Here it is! */
        goto allgut;                                                                        /* No more living elements */
living: ;                                                                                   /* Processing the next living element */
        for (k = 0; k != 5; k ++) SimF[IndSim][k] = SimF[i][k];                             /* Copying this living element into the compressed position */
        IndSim ++;                                                                          /* The next compressed position */
        l = i+1;                                                                            /* From where to look for the next living element */
        if (l == NSimF) goto allgut;                                                        /* No more living elements left */
      }
    }
allgut: NSimF = IndSim;
  if (NSimF == 0) { fprintf(fout,"All similarities filtered out!\n"); continue; }           /* If no finished similarities survived, proceed to the next orientation/query */

/* Bubble sorting should be fast enough because similarities are almost perfectly ordered already */
  if (NSimF != 1)
  {
    for (;;)                                                                                /* Bubble sorting, according to starts on the query sequence */
    {
      i = 0;                                                                                /* Counter of swaps */
      for (IndSim = 0; IndSim != NSimF-1; IndSim ++)                                        /* Cycle by all pairs of consecutive similarities */
      if (SimF[IndSim][2] > SimF[IndSim+1][2])                                              /* Incorrect order */
      {
        for (k = 0; k != 5; k ++)                                                           /* Swapping consecutive similarities */
        {
          l = SimF[IndSim][k];
          SimF[IndSim][k] = SimF[IndSim+1][k];
          SimF[IndSim+1][k] = l;
        }
        i ++;                                                                               /* Counting swappings */
      }
      if (i == 0) break;                                                                    /* No swaps, ordering done */
    }
  }

/*  Second step of post-processing - merging "close" similarities */
/*  This step could be done in many different ways. I consider only pairs of successive similarities (A and B), assuming that
    they are ordered according to their starts in query sequence (B follows A) and that there are no dead elements in the list.
    Merging means constructing the "enclosing" similarity, with each coordinate of its start being minimal and each
    coordinate of its finish being maximal. If B is subordinate to A (B starts after A and B stops before A in both
    sequences), this mean that B is disregarded. The "enclosing" similarity is recorded in place of B.
    We distinguish thee cases of mutual locations of A and B (draw rectangles around them!), and totally 6 subcases - I, IIa, IIb, IIIa, IIIb, and IIIC. */
  for (IndSim = 0; IndSim != NSimF-1; IndSim ++)                                     /* Cycle by "similarity A" */
  {

    for (i = IndSim+1; i != NSimF; i ++)                                             /* Cycle by possible "similarities B" for a particular similarity A */
    {
      if (SimF[i][0] < SimF[IndSim][0]) continue;                                    /* If B begins in database before A, we never want to merge - remember, B always begins after A in query */
      dist1 = SimF[i][0] - SimF[IndSim][1];                                          /* Distances between beginning of similarity B and end of similarity A in database and query */
      dist2 = SimF[i][2] - SimF[IndSim][3];                                          /* Depending on these distances, there are 3 cases */
      if (dist2 > MaxDistPost) break;                                                /* This possible B is too far away in query sequence, and the subsequent ones will also be too far away */
      if (dist1 >= dist2) gap = dist1 - dist2; else gap = dist2 - dist1;             /* gap is absolute value of the difference between indices of diagonals of the beginning of B and end of A. */
      if (dist1 > 0 && dist2 > 0)                                                    /* Case I - B follows A on both sequences, no subcases */
      {
        if (dist1 >= dist2) mis = dist2; else mis = dist1;                           /* mis is the number of nucleotides between perpendicular diagonals containing B and A */
        if (gap+mis*CoeffMisPost > MaxDistPost) continue;                            /* B too far away from A, do not merge them, try the next possible B */
      }
      else if (dist1 <= 0 && dist2 <= 0)                                             /* Case III - the opposite - the beginning of B precedes the end of A in both sequences. There are 3 subcases */
      {
        if (SimF[i][0] - SimF[IndSim][0] > 0 &&
            SimF[i][1] - SimF[IndSim][1] < 0 &&
            SimF[i][3] - SimF[IndSim][3] < 0) goto merge;                            /* Subcase of case III - B is nested within A (B rectangle is contained within A rectangle), merge them (i. e., kill B) */
        if (gap > MaxDistPost) continue;                                             /* Simplistic treatment - ignore the value of overlap and treat all other subcases of III in the same way, this is for Raquel to look at */
      }
      else                                                                           /* Case II - the intermediate case - the beginning of B precedes the end of A in only one sequence. There are 2 subcases */
      {
        if (dist2 > 0 &&
            SimF[i][1] - SimF[IndSim][0] < 0) continue;                              /* Subcase of case II - B is fully above and fully to the left of A, never merge */
        if (gap > MaxDistPost) continue;                                             /* Simplistic treatment - ignore the value of overlap and treat both subcases of II in the same way, for Raquel to look at */
      }
merge: ;                                                                             /* Merging means creating an "enclosing" similarity */
      if (SimF[i][0] > SimF[IndSim][0]) SimF[i][0] = SimF[IndSim][0];                /* Choose the earliest start in database sequence; */
      if (SimF[i][1] < SimF[IndSim][1]) SimF[i][1] = SimF[IndSim][1];                /* Choose the latest end in database sequence */
      SimF[i][2] = SimF[IndSim][2];                                                  /* The earliest start in query sequence is in A */
      if (SimF[i][3] < SimF[IndSim][3]) SimF[i][3] = SimF[IndSim][3];                /* Choose the latest end in query sequence */
      SimF[i][4] = SimF[i][4] + SimF[IndSim][4];                                     /* I am not sure the weights should be added, but why not */
      SimF[IndSim][4] = -1; break;                                                   /* A is now dead, as I do not try other possible similarities B is a merger occurred */
    }
  }

/* read masked sequences again, if they will be needed - the corresponding arrays were used to store overlap information for pre-processing */
    if (PrintSeq == 1)
    {
      if ((fseqM1 = fopen("seq1M.txt","r")) == NULL) { fprintf(fout," no seq1M-4 "); goto quit; }
      if ((fseqM2 = fopen("seq2M.txt","r")) == NULL) { fprintf(fout," no seq2M-3 "); goto quit; }
      for (i = 0; i != L1; i++) seq1[i] = getc(fseqM1); for (i = 0; i != L2; i++) seq2[i] = getc(fseqM2);
      fclose(fseqM1); fclose(fseqM2);
    }

 } /* end of post-processing */

/*   Printing the results */
  i = 0;
  for (IndSim = 0; IndSim != NSimF; IndSim ++)
  {
    if (SimF[IndSim][4] == -1) continue;
    i ++;
    if (ori == 0) fprintf(fout," %5li %10li %10li %10li %10li %10li\n", i, SimF[IndSim][0]+1, SimF[IndSim][1]+1, SimF[IndSim][2]+1,  SimF[IndSim][3]+1,  SimF[IndSim][4]);
    if (ori == 1) fprintf(fout," %5li %10li %10li %10li %10li %10li\n", i, SimF[IndSim][0],   SimF[IndSim][1],   L2-SimF[IndSim][2], L2-SimF[IndSim][3], SimF[IndSim][4]);
    if (PrintSeq == 1)
    {
      for (l = SimF[IndSim][0]; l != SimF[IndSim][1]+1; l++) fprintf(fout,"%c", SeqToPrint(seq1[l])); fprintf(fout,"%\n");
      for (l = SimF[IndSim][2]; l != SimF[IndSim][3]+1; l++) fprintf(fout,"%c", SeqToPrint(seq2[l])); fprintf(fout,"%\n");
    }
  }
} /* END_OF_ORIENTATION LOOP */
  if (LastQuery == 1) break;
} /* END_OF_QUERY SEQUENCES LOOP */

quit: fprintf(fout,"\nAbzac");
  fclose(fseq2); fclose(fout);
  return 0;
}

/*   Reading a sequence, ignoring white spaces and numbers and accepting all other characters */
char ReadGoodChar (FILE *fseq)
{
  char c;
  for (;;)
  {
    c = getc(fseq);
	if (c == ' ' || c == '	' || c == '\n' || c == '/' || c == '\r' || c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || c == '5' || c == '6' || c == '7' || c == '8' || c == '9') continue;
    return c;
  }
}

/*   Simple functions, dealing with symbols */
long Good           (char c) { long R; R =  0; if (c == 'A') R = 1;   else if (c == 'T') R = 1;   else if (c == 'G') R = 1;   else if (c == 'C') R = 1;   return R; }
char Comp           (char c) { char R; R =  c; if (c == 'A') R = 'T'; else if (c == 'T') R = 'A'; else if (c == 'G') R = 'C'; else if (c == 'C') R = 'G';
                                               if (c == 'a') R = 't'; else if (c == 't') R = 'a'; else if (c == 'g') R = 'c'; else if (c == 'c') R = 'g';
                                               if (c == 'e') R = 'f'; else if (c == 'f') R = 'e'; else if (c == 'i') R = 'j'; else if (c == 'j') R = 'i'; return R; }
long LetterToNumber (char c) { long R; R = -1; if (c == 'A') R = 0;   else if (c == 'T') R = 1;   else if (c == 'G') R = 2;   else if (c == 'C') R = 3;   return R; }

/*  Replacing lower-case letters in the input file, either by upper-case letters (if original masking, if any, is to be ignored) or by internal symbols (to avoid mix-ups with internal masking) */
char FileToSeq (long LowCase, char c)
{
  char R;

  R = c;
  if (LowCase == 0)
  {
    if (c == 'a') R = 'A'; else if (c == 't') R = 'T'; else if (c == 'g') R = 'G'; else if (c == 'c') R = 'C'; return R;
  }
  else
  {
    if (c == 'a') R = 'e'; else if (c == 't') R = 'f'; else if (c == 'g') R = 'i'; else if (c == 'c') R = 'j'; return R;
  }
}

char UpperToLower    (char c) { char R; R = c;  if (c == 'A') R = 'a'; else if (c == 'T') R = 't'; else if (c == 'G') R = 'g'; else if (c == 'C') R = 'c'; return R; }
char LowerToUpper    (char c) { char R; R = c;  if (c == 'a') R = 'A'; else if (c == 't') R = 'T'; else if (c == 'g') R = 'G'; else if (c == 'c') R = 'C'; return R; }
char SeqToPrint      (char c) { char R; R = c;  if (c == 'e') R = 'a'; else if (c == 'f') R = 't'; else if (c == 'i') R = 'g'; else if (c == 'j') R = 'c'; return R; }

/*   Retrieving sequence from temporary storage file for further work (not for output), reverting internal masking and possibly invert-complementing */
void RetrieveSeq(FILE *fseqM, long L, long IC, char *seq)
{
  long i;
  char c;

  for (i = 0; i != L; i ++) { c = getc(fseqM); seq[i] = LowerToUpper(c); }

  if (IC == 1)
    for (i = 0; i != (L+1)/2; i ++)
    {
      c = seq[i];
      seq[i] = Comp(seq[L-i-1]);
      seq[L-i-1] = Comp(c);
    }
}

/*   Extracting sequence name from FASTA line */
long ReadFastA (FILE *fseq, char *Name)
{
  long i;
  char c;

  for (i = 0; ; i ++)
  {
    c = getc(fseq);
    if (i == 100 || c == ' ' || c == '	' || c == '\n' || c == '/' || c == '\r') return i;
    Name[i] = c;
  }
}

/*   Scan sequence and record the number of occurrences of each KM word into array of 1-bite numbers. Also, calculate nucleotide composition. */
void KMWordCover (long KM, long KM4, long L, char *seq, long *LetFreq,  unsigned char *Mask4K)
{
  long Lead, NWord, Mult, i, k;

  Lead = 0; NWord = 0;                                              /* Initialization for accumulating the lexicographical number NWord of a KM word */
  for (k = 0; k != 4; k ++) LetFreq[k] = 0;                         /* Initialize nucleotide compositions */
  for (i = 0; i != L; i++)                                          /* Scan the sequence */
  {
	if (Good(seq[i]) == 0) { Lead = 0; NWord = 0; }                 /* If a letter is bad (not A, T, G, or C), reinitialize */
	else                                                            /* If a letter is good */
	{
	  Mult = LetterToNumber(seq[i]);                                /* Take its number */
      LetFreq[Mult] ++;                                             /* Record it into nucleotide composition */
	  if (Lead < KM) NWord = NWord*4+Mult;                          /* Calculate NWord of an incomplete KM word */
	  else NWord = 4*(NWord % (KM4/4)) + Mult;                      /* Calculate NWord of a complete KM word - apparently, all this works correctly! */
	  Lead ++;                                                      /* Increment the counter of KM word completeness */
	}
	if (Lead < KM) { /* fprintf (fout, " %12li \n",    -1); */ ; }
	else           { /* fprintf (fout, " %12li \n", NWord); */ if (Mask4K[NWord] != 255) Mask4K[NWord] ++; } /* Increment the array of KM word occurrences */
  }
}

/*   Scan sequences 1 and 2, masking KM words that are too common */
void MaskingLight (long KM, long KM4, long L, long Filter, unsigned char *Mask4K, long double (*P)[4], char *seq)
{
  long Lead, NWord, Mult, i, k, LetNum[4], Condition, m, j;
  long double E;
  char c;

  Lead = 0; NWord = 0;                                                                      /* Initialization for accumulating the lexicographical number NWord of a KM word */
  for (k = 0; k != 4; k ++) LetNum[k] = 0;                                                  /* Initialize nucleotide numbers within the current KM word */
  for (i = 0; i != L; i++)                                                                  /* Scan the sequence */
  {
    c = seq[i];                                                                             /* Current letter */
	if (Good(c) == 0) { Lead = 0; NWord = 0; for (k = 0; k != 4; k ++) LetNum[k] = 0; }     /* If a letter is bad (not A, T, G, or C), reinitialize, including nucleotide numbers */
	else                                                                                    /* If a letter is good */
	{
      Mult = LetterToNumber(c);                                                             /* Take its number */
	  LetNum[Mult] ++;                                                                      /* Record it into counters of nucleotides within the current KM word */
	  if (Lead < KM) NWord = NWord*4+Mult;                                                  /* Calculate NWord of an incomplete KM word */
	  else NWord = 4*(NWord % (KM4/4)) + Mult;                                              /* Calculate NWord of a complete KM word - apparently, all this works correctly! */
	  Lead ++;                                                                              /* Increment the counter of KM word completeness */
    }
	if (Lead >= KM)                                                                         /* Process only complete KM words */
	{
      E = L*P[LetNum[0]][0]*P[LetNum[1]][1]*P[LetNum[2]][2]*P[LetNum[3]][3];                /* Expected number of occurrences of the KM word in sequence 1 */
	  Condition = 0; m = Mask4K[NWord];                                                     /* Condition for masking; do not do arithmetic with unsigned short! */
	  if (m > Filter) Condition = 1;                                                        /* Mask if the KM word occurred too many times in at least one sequence */
	  if (Condition == 1) { for (j = i; j != i-KM; j--) seq[j] = UpperToLower(seq[j]); }    /* Masking KM symbols */
	  LetNum[LetterToNumber(LowerToUpper(seq[i-KM+1]))] --;                                 /* Decrement the letter counter */
	}
  }
}

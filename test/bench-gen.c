/* M5 part A (design item 1, Q-M5-6): bench-gen N writes to stdout a
   program with a Log of N entries, one write and one read for each of the 18
   queries. The entries take the form of examples/crm.ledger:31 and of d3
   cases 83 and 84, in a cycle of 8 families, and each entry has a distinct
   text (its index). The refs of the queries name no entry, thus each answer
   stays short and the output holds the log once. The make target bench runs
   build/ledgerc on the files of N = 1000, 4000 and 16000. */
#include <stdio.h>
#include <stdlib.h>

#define BENCH_MAX 1000000UL

int main(int argc, char **argv) {
  const char *const head[] = {
      "-- M5 part A (design item 1): a bench log, one write and the 18 queries.",
      /* acme names the Party record of entry 0 ("Org 0"; the same entry for each N), as in d3 case 84. */
      "def acme : Ref kindParty := refTo (hashOf \"e04ce1125348606897ddbfb317fbf8138dc6eeda3a1a24314ab501ef477ca866\")",
      "def pat : Ref kindParty := refTo (hashOf \"party-pat\")",
      "def deal : Ref kindCommercial := refTo (hashOf \"deal-none\")",
      "def missing : Hash := hashOf \"entry-none\"",
      "def note : Event := makeEvent eventNoteAdded (subjectCommercial deal) none none attrsEnd none",
      "def plan : Commercial := makeCommercial commercialDeal \"Deal none\" acme \"qualify\" (some 1000) \"USD\" none "
      "statusOpen attrsEnd none",
  };
  const char *const entries[] = {
      "makeEntry none (actorAgent \"bench\") (createsParty (makeParty partyOrg \"Org %lu\" none nil attrsEnd none "
      "none))",
      "makeEntry none (actorHuman acme) (createsParty (makeParty partyPerson \"Person %lu\" none nil attrsEnd none "
      "none))",
      "makeEntry none (actorAgent \"bench\") (createsCommercial (makeCommercial commercialDeal \"Deal %lu\" acme "
      "\"qualify\" (some 1000) \"USD\" (some \"2026-11-01\") statusOpen attrsEnd none))",
      "makeEntry none (actorHuman acme) (createsEvent (makeEvent eventNoteAdded (subjectCommercial deal) none none "
      "(attrsField \"note\" (valueText \"Note %lu\") attrsEnd) none))",
      "makeEntry none (actorAgent \"bench\") (createsCommitment (makeCommitment deal commitmentDate \"Term %lu\" "
      "(valueText \"2027-01-31\") none commitmentAgreed none (makeProvenance none none (some 40))))",
      "makeEntry none (actorHuman acme) (createsMembership (makeMembership pat acme (some \"Role %lu\") flagYes none "
      "(makeProvenance none none (some 95)) attrsEnd))",
      "makeEntry none (actorAgent \"bench\") (createsCommercial (makeCommercial commercialDeal \"Deal %lu\" acme "
      "\"propose\" (some 500) \"USD\" none statusOpen attrsEnd none))",
      "makeEntry none (actorHuman acme) (createsAssignment (makeAssignment (accountParty acme) pat roleOwner none "
      "none (makeProvenance (some (refTo (hashOf \"mail %lu\"))) none (some 95))))",
  };
  const char *const tail[] = {
      "def stale : Write := makeWrite (actorAgent \"bench\") (some (hashOf \"head-none\")) (commandRecord note)",
      "def step : Step := write book stale",
      "def replayed : Log := read Log book (queryReplay (momentAsOf missing))",
      "def after : Log := read Log book (queryTail (momentAsOf missing))",
      "def acts : List (Ref kindEvent) := read (List (Ref kindEvent)) book (queryAuditByActor (actorHuman pat))",
      "def found : Option Commercial := read (Option Commercial) book (queryCommercial deal momentNow)",
      "def sound : Flag := read Flag book (queryProjectionSound deal plan)",
      "def terms : List (Ref kindCommitment) := read (List (Ref kindCommitment)) book (queryTermsInForce deal "
      "momentNow)",
      "def history : List (Ref kindCommitment) := read (List (Ref kindCommitment)) book (queryTermHistory (refTo "
      "(hashOf \"term-none\")))",
      "def reconciled : Flag := read Flag book (queryAmountReconciled deal)",
      "def discount : Option Nat := read (Option Nat) book (queryDiscountPct deal)",
      "def members : List (Ref kindMembership) := read (List (Ref kindMembership)) book (queryMembersOf acme "
      "(momentAsOf missing))",
      "def employer : Option (Ref kindParty) := read (Option (Ref kindParty)) book (queryEmployer pat momentNow)",
      "def changes : List (Ref kindParty) := read (List (Ref kindParty)) book (queryJobChanges momentNow)",
      "def byStage : List Bucket := read (List Bucket) book (queryPipeline pipelineByStage momentNow)",
      "def stats : List StageStat := read (List StageStat) book queryStageStats",
      "def staleDeals : List (Ref kindCommercial) := read (List (Ref kindCommercial)) book (queryStaleDeals 0)",
      "def renewals : List Renewal := read (List Renewal) book queryRenewals",
      "def account : Account360 := read Account360 book (queryAccount360 acme momentNow)",
      "def queue : List Hash := read (List Hash) book (queryReviewQueue 0)",
  };
  char *end = NULL;
  unsigned long count = argc == 2 ? strtoul(argv[1], &end, 10) : 0;
  if (argc != 2 || end == NULL || *end != '\0' || count == 0 || count > BENCH_MAX) {
    fprintf(stderr, "usage: bench-gen N (N from 1 to %lu)\n", BENCH_MAX);
    return 2;
  }
  size_t heads = sizeof head / sizeof head[0];
  size_t families = sizeof entries / sizeof entries[0];
  size_t tails = sizeof tail / sizeof tail[0];
  for (size_t line = 0; line < heads; line++) printf("%s\n", head[line]);
  printf("def book : Log :=");
  for (unsigned long index = 0; index < count; index++) {
    printf("\n  cons (");
    printf(entries[index % families], index);
    printf(") (");
  }
  printf("nil");
  for (unsigned long index = 0; index < count; index++) printf(")");
  printf("\n");
  for (size_t line = 0; line < tails; line++) printf("%s\n", tail[line]);
  return 0;
}

/* literals.c: the literal texts of the compiler as constant Nat byte
   arrays (declared in literals.h). This file is the source; edit it by
   hand. A tool first generated it from the mech compiler's literals.mech. */
#include "ledger.h"

/* "Nat" */
static const Nat sNat_items[] = {
  'N', 'a', 't',
};
const Text sNat = {sNat_items, 3};

/* "Text" */
static const Nat sText_items[] = {
  'T', 'e', 'x', 't',
};
const Text sText = {sText_items, 4};

/* "Flag" */
static const Nat sFlag_items[] = {
  'F', 'l', 'a', 'g',
};
const Text sFlag = {sFlag_items, 4};

/* "Value" */
static const Nat sValue_items[] = {
  'V', 'a', 'l', 'u', 'e',
};
const Text sValue = {sValue_items, 5};

/* "Values" */
static const Nat sValues_items[] = {
  'V', 'a', 'l', 'u', 'e', 's',
};
const Text sValues = {sValues_items, 6};

/* "Attrs" */
static const Nat sAttrs_items[] = {
  'A', 't', 't', 'r', 's',
};
const Text sAttrs = {sAttrs_items, 5};

/* "Kind" */
static const Nat sKind_items[] = {
  'K', 'i', 'n', 'd',
};
const Text sKind = {sKind_items, 4};

/* "Option" */
static const Nat sOption_items[] = {
  'O', 'p', 't', 'i', 'o', 'n',
};
const Text sOption = {sOption_items, 6};

/* "List" */
static const Nat sList_items[] = {
  'L', 'i', 's', 't',
};
const Text sList = {sList_items, 4};

/* "Prod" */
static const Nat sProd_items[] = {
  'P', 'r', 'o', 'd',
};
const Text sProd = {sProd_items, 4};

/* "Sum" */
static const Nat sSum_items[] = {
  'S', 'u', 'm',
};
const Text sSum = {sSum_items, 3};

/* "def" */
static const Nat sdef_items[] = {
  'd', 'e', 'f',
};
const Text sdef = {sdef_items, 3};

/* "rec" */
static const Nat srec_items[] = {
  'r', 'e', 'c',
};
const Text srec = {srec_items, 3};

/* "mu" */
static const Nat smu_items[] = {
  'm', 'u',
};
const Text smu = {smu_items, 2};

/* "axiom" */
static const Nat saxiom_items[] = {
  'a', 'x', 'i', 'o', 'm',
};
const Text saxiom = {saxiom_items, 5};

/* "poly" */
static const Nat spoly_items[] = {
  'p', 'o', 'l', 'y',
};
const Text spoly = {spoly_items, 4};

/* "specialize" */
static const Nat sspecialize_items[] = {
  's', 'p', 'e', 'c', 'i', 'a', 'l', 'i', 'z', 'e',
};
const Text sspecialize = {sspecialize_items, 10};

/* "textEnd" */
static const Nat stextEnd_items[] = {
  't', 'e', 'x', 't', 'E', 'n', 'd',
};
const Text stextEnd = {stextEnd_items, 7};

/* "textByte" */
static const Nat stextByte_items[] = {
  't', 'e', 'x', 't', 'B', 'y', 't', 'e',
};
const Text stextByte = {stextByte_items, 8};

/* "flagNo" */
static const Nat sflagNo_items[] = {
  'f', 'l', 'a', 'g', 'N', 'o',
};
const Text sflagNo = {sflagNo_items, 6};

/* "flagYes" */
static const Nat sflagYes_items[] = {
  'f', 'l', 'a', 'g', 'Y', 'e', 's',
};
const Text sflagYes = {sflagYes_items, 7};

/* "none" */
static const Nat snone_items[] = {
  'n', 'o', 'n', 'e',
};
const Text snone = {snone_items, 4};

/* "some" */
static const Nat ssome_items[] = {
  's', 'o', 'm', 'e',
};
const Text ssome = {ssome_items, 4};

/* "nil" */
static const Nat snil_items[] = {
  'n', 'i', 'l',
};
const Text snil = {snil_items, 3};

/* "cons" */
static const Nat scons_items[] = {
  'c', 'o', 'n', 's',
};
const Text scons = {scons_items, 4};

/* "valueNull" */
static const Nat svalueNull_items[] = {
  'v', 'a', 'l', 'u', 'e', 'N', 'u', 'l', 'l',
};
const Text svalueNull = {svalueNull_items, 9};

/* "valueFlag" */
static const Nat svalueFlag_items[] = {
  'v', 'a', 'l', 'u', 'e', 'F', 'l', 'a', 'g',
};
const Text svalueFlag = {svalueFlag_items, 9};

/* "valueNat" */
static const Nat svalueNat_items[] = {
  'v', 'a', 'l', 'u', 'e', 'N', 'a', 't',
};
const Text svalueNat = {svalueNat_items, 8};

/* "valueText" */
static const Nat svalueText_items[] = {
  'v', 'a', 'l', 'u', 'e', 'T', 'e', 'x', 't',
};
const Text svalueText = {svalueText_items, 9};

/* "valueItems" */
static const Nat svalueItems_items[] = {
  'v', 'a', 'l', 'u', 'e', 'I', 't', 'e', 'm', 's',
};
const Text svalueItems = {svalueItems_items, 10};

/* "valueAttrs" */
static const Nat svalueAttrs_items[] = {
  'v', 'a', 'l', 'u', 'e', 'A', 't', 't', 'r', 's',
};
const Text svalueAttrs = {svalueAttrs_items, 10};

/* "valuesEnd" */
static const Nat svaluesEnd_items[] = {
  'v', 'a', 'l', 'u', 'e', 's', 'E', 'n', 'd',
};
const Text svaluesEnd = {svaluesEnd_items, 9};

/* "valuesItem" */
static const Nat svaluesItem_items[] = {
  'v', 'a', 'l', 'u', 'e', 's', 'I', 't', 'e', 'm',
};
const Text svaluesItem = {svaluesItem_items, 10};

/* "attrsEnd" */
static const Nat sattrsEnd_items[] = {
  'a', 't', 't', 'r', 's', 'E', 'n', 'd',
};
const Text sattrsEnd = {sattrsEnd_items, 8};

/* "attrsField" */
static const Nat sattrsField_items[] = {
  'a', 't', 't', 'r', 's', 'F', 'i', 'e', 'l', 'd',
};
const Text sattrsField = {sattrsField_items, 10};

/* "pair" */
static const Nat spair_items[] = {
  'p', 'a', 'i', 'r',
};
const Text spair = {spair_items, 4};

/* "inl" */
static const Nat sinl_items[] = {
  'i', 'n', 'l',
};
const Text s_inl = {sinl_items, 3};

/* "inr" */
static const Nat sinr_items[] = {
  'i', 'n', 'r',
};
const Text sinr = {sinr_items, 3};

/* "kindParty" */
static const Nat skindParty_items[] = {
  'k', 'i', 'n', 'd', 'P', 'a', 'r', 't', 'y',
};
const Text skindParty = {skindParty_items, 9};

/* "kindMembership" */
static const Nat skindMembership_items[] = {
  'k', 'i', 'n', 'd', 'M', 'e', 'm', 'b', 'e', 'r', 's', 'h', 'i', 'p',
};
const Text skindMembership = {skindMembership_items, 14};

/* "kindCommercial" */
static const Nat skindCommercial_items[] = {
  'k', 'i', 'n', 'd', 'C', 'o', 'm', 'm', 'e', 'r', 'c', 'i', 'a', 'l',
};
const Text skindCommercial = {skindCommercial_items, 14};

/* "kindCommitment" */
static const Nat skindCommitment_items[] = {
  'k', 'i', 'n', 'd', 'C', 'o', 'm', 'm', 'i', 't', 'm', 'e', 'n', 't',
};
const Text skindCommitment = {skindCommitment_items, 14};

/* "kindArtifact" */
static const Nat skindArtifact_items[] = {
  'k', 'i', 'n', 'd', 'A', 'r', 't', 'i', 'f', 'a', 'c', 't',
};
const Text skindArtifact = {skindArtifact_items, 12};

/* "kindEvent" */
static const Nat skindEvent_items[] = {
  'k', 'i', 'n', 'd', 'E', 'v', 'e', 'n', 't',
};
const Text skindEvent = {skindEvent_items, 9};

/* "kindAssignment" */
static const Nat skindAssignment_items[] = {
  'k', 'i', 'n', 'd', 'A', 's', 's', 'i', 'g', 'n', 'm', 'e', 'n', 't',
};
const Text skindAssignment = {skindAssignment_items, 14};

/* "kindPolicy" */
static const Nat skindPolicy_items[] = {
  'k', 'i', 'n', 'd', 'P', 'o', 'l', 'i', 'c', 'y',
};
const Text skindPolicy = {skindPolicy_items, 10};

/* "compiler fuel exhausted" */
static const Nat eFuel_items[] = {
  'c', 'o', 'm', 'p', 'i', 'l', 'e', 'r', ' ', 'f', 'u', 'e', 'l', ' ', 'e', 'x', 'h', 'a', 'u',
  's', 't', 'e', 'd',
};
const Text eFuel = {eFuel_items, 23};

/* "invalid UTF-8" */
static const Nat eUtf8_items[] = {
  'i', 'n', 'v', 'a', 'l', 'i', 'd', ' ', 'U', 'T', 'F', '-', '8',
};
const Text eUtf8 = {eUtf8_items, 13};

/* "unexpected source byte" */
static const Nat eCharacter_items[] = {
  'u', 'n', 'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 's', 'o', 'u', 'r', 'c', 'e', ' ', 'b',
  'y', 't', 'e',
};
const Text eCharacter = {eCharacter_items, 22};

/* "unterminated or invalid string" */
static const Nat eString_items[] = {
  'u', 'n', 't', 'e', 'r', 'm', 'i', 'n', 'a', 't', 'e', 'd', ' ', 'o', 'r', ' ', 'i', 'n', 'v',
  'a', 'l', 'i', 'd', ' ', 's', 't', 'r', 'i', 'n', 'g',
};
const Text eString = {eString_items, 30};

/* "unsupported string escape" */
static const Nat eEscape_items[] = {
  'u', 'n', 's', 'u', 'p', 'p', 'o', 'r', 't', 'e', 'd', ' ', 's', 't', 'r', 'i', 'n', 'g', ' ',
  'e', 's', 'c', 'a', 'p', 'e',
};
const Text eEscape = {eEscape_items, 25};

/* "Nat exceeds 1073741823" */
static const Nat eNumber_items[] = {
  'N', 'a', 't', ' ', 'e', 'x', 'c', 'e', 'e', 'd', 's', ' ', '1', '0', '7', '3', '7', '4', '1',
  '8', '2', '3',
};
const Text eNumber = {eNumber_items, 22};

/* "expected a supported type" */
static const Nat eType_items[] = {
  'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 'a', ' ', 's', 'u', 'p', 'p', 'o', 'r', 't', 'e',
  'd', ' ', 't', 'y', 'p', 'e',
};
const Text eType = {eType_items, 25};

/* "term does not have the declared type" */
static const Nat eTerm_items[] = {
  't', 'e', 'r', 'm', ' ', 'd', 'o', 'e', 's', ' ', 'n', 'o', 't', ' ', 'h', 'a', 'v', 'e', ' ',
  't', 'h', 'e', ' ', 'd', 'e', 'c', 'l', 'a', 'r', 'e', 'd', ' ', 't', 'y', 'p', 'e',
};
const Text eTerm = {eTerm_items, 36};

/* "unknown name or constructor" */
static const Nat eUnknown_items[] = {
  'u', 'n', 'k', 'n', 'o', 'w', 'n', ' ', 'n', 'a', 'm', 'e', ' ', 'o', 'r', ' ', 'c', 'o', 'n',
  's', 't', 'r', 'u', 'c', 't', 'o', 'r',
};
const Text eUnknown = {eUnknown_items, 27};

/* "duplicate definition name" */
static const Nat eDuplicate_items[] = {
  'd', 'u', 'p', 'l', 'i', 'c', 'a', 't', 'e', ' ', 'd', 'e', 'f', 'i', 'n', 'i', 't', 'i', 'o',
  'n', ' ', 'n', 'a', 'm', 'e',
};
const Text eDuplicate = {eDuplicate_items, 25};

/* "duplicate attribute key" */
static const Nat eField_items[] = {
  'd', 'u', 'p', 'l', 'i', 'c', 'a', 't', 'e', ' ', 'a', 't', 't', 'r', 'i', 'b', 'u', 't', 'e',
  ' ', 'k', 'e', 'y',
};
const Text eField = {eField_items, 23};

/* "expected def NAME : TYPE := TERM" */
static const Nat eDef_items[] = {
  'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 'd', 'e', 'f', ' ', 'N', 'A', 'M', 'E', ' ', ':',
  ' ', 'T', 'Y', 'P', 'E', ' ', ':', '=', ' ', 'T', 'E', 'R', 'M',
};
const Text eDef = {eDef_items, 32};

/* "expected closing parenthesis" */
static const Nat eClose_items[] = {
  'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 'c', 'l', 'o', 's', 'i', 'n', 'g', ' ', 'p', 'a',
  'r', 'e', 'n', 't', 'h', 'e', 's', 'i', 's',
};
const Text eClose = {eClose_items, 28};

/* "reserved definition name" */
static const Nat eReserved_items[] = {
  'r', 'e', 's', 'e', 'r', 'v', 'e', 'd', ' ', 'd', 'e', 'f', 'i', 'n', 'i', 't', 'i', 'o', 'n',
  ' ', 'n', 'a', 'm', 'e',
};
const Text eReserved = {eReserved_items, 24};

/* "textByte requires a byte below 256" */
static const Nat eByte_items[] = {
  't', 'e', 'x', 't', 'B', 'y', 't', 'e', ' ', 'r', 'e', 'q', 'u', 'i', 'r', 'e', 's', ' ', 'a',
  ' ', 'b', 'y', 't', 'e', ' ', 'b', 'e', 'l', 'o', 'w', ' ', '2', '5', '6',
};
const Text eByte = {eByte_items, 34};

/* "unexpected token after term" */
static const Nat eTrailing_items[] = {
  'u', 'n', 'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 't', 'o', 'k', 'e', 'n', ' ', 'a', 'f',
  't', 'e', 'r', ' ', 't', 'e', 'r', 'm',
};
const Text eTrailing = {eTrailing_items, 27};

/* "{\"ledger-lang\":1,\"instances\":[" */
static const Nat jHeader_items[] = {
  '{', '"', 'l', 'e', 'd', 'g', 'e', 'r', '-', 'l', 'a', 'n', 'g', '"', ':', '1', ',', '"', 'i',
  'n', 's', 't', 'a', 'n', 'c', 'e', 's', '"', ':', '[',
};
const Text jHeader = {jHeader_items, 30};

/* "]}" */
static const Nat jEnd_items[] = {
  ']', '}',
};
const Text jEnd = {jEnd_items, 2};

/* "{\"error\":{\"byte\":" */
static const Nat jError_items[] = {
  '{', '"', 'e', 'r', 'r', 'o', 'r', '"', ':', '{', '"', 'b', 'y', 't', 'e', '"', ':',
};
const Text jError = {jError_items, 17};

/* ",\"message\":" */
static const Nat jMessage_items[] = {
  ',', '"', 'm', 'e', 's', 's', 'a', 'g', 'e', '"', ':',
};
const Text jMessage = {jMessage_items, 11};

/* "}}" */
static const Nat jErrorEnd_items[] = {
  '}', '}',
};
const Text jErrorEnd = {jErrorEnd_items, 2};

/* "name" */
static const Nat kName_items[] = {
  'n', 'a', 'm', 'e',
};
const Text kName = {kName_items, 4};

/* "type" */
static const Nat kType_items[] = {
  't', 'y', 'p', 'e',
};
const Text kType = {kType_items, 4};

/* "value" */
static const Nat kValue_items[] = {
  'v', 'a', 'l', 'u', 'e',
};
const Text kValue = {kValue_items, 5};

/* "first" */
static const Nat kFirst_items[] = {
  'f', 'i', 'r', 's', 't',
};
const Text kFirst = {kFirst_items, 5};

/* "second" */
static const Nat kSecond_items[] = {
  's', 'e', 'c', 'o', 'n', 'd',
};
const Text kSecond = {kSecond_items, 6};

/* "inl" */
static const Nat kInl_items[] = {
  'i', 'n', 'l',
};
const Text kInl = {kInl_items, 3};

/* "inr" */
static const Nat kInr_items[] = {
  'i', 'n', 'r',
};
const Text kInr = {kInr_items, 3};

/* "some" */
static const Nat kSome_items[] = {
  's', 'o', 'm', 'e',
};
const Text kSome = {kSome_items, 4};

/* "null" */
static const Nat jNull_items[] = {
  'n', 'u', 'l', 'l',
};
const Text jNull = {jNull_items, 4};

/* "true" */
static const Nat jTrue_items[] = {
  't', 'r', 'u', 'e',
};
const Text jTrue = {jTrue_items, 4};

/* "false" */
static const Nat jFalse_items[] = {
  'f', 'a', 'l', 's', 'e',
};
const Text jFalse = {jFalse_items, 5};

/* "output budget exceeded" */
static const Nat eOutput_items[] = {
  'o', 'u', 't', 'p', 'u', 't', ' ', 'b', 'u', 'd', 'g', 'e', 't', ' ', 'e', 'x', 'c', 'e', 'e',
  'd', 'e', 'd',
};
const Text eOutput = {eOutput_items, 22};

/* "argument needs parentheses" */
static const Nat eParen_items[] = {
  'a', 'r', 'g', 'u', 'm', 'e', 'n', 't', ' ', 'n', 'e', 'e', 'd', 's', ' ', 'p', 'a', 'r', 'e',
  'n', 't', 'h', 'e', 's', 'e', 's',
};
const Text eParen = {eParen_items, 26};

/* "Type" */
static const Nat sType_items[] = {
  'T', 'y', 'p', 'e',
};
const Text sType = {sType_items, 4};

/* "fun" */
static const Nat sfun_items[] = {
  'f', 'u', 'n',
};
const Text sfun = {sfun_items, 3};

/* "Sigma" */
static const Nat sSigma_items[] = {
  'S', 'i', 'g', 'm', 'a',
};
const Text sSigma = {sSigma_items, 5};

/* "pack" */
static const Nat spack_items[] = {
  'p', 'a', 'c', 'k',
};
const Text spack = {spack_items, 4};

/* "witness" */
static const Nat switness_items[] = {
  'w', 'i', 't', 'n', 'e', 's', 's',
};
const Text switness = {switness_items, 7};

/* "payload" */
static const Nat spayload_items[] = {
  'p', 'a', 'y', 'l', 'o', 'a', 'd',
};
const Text spayload = {spayload_items, 7};

/* "Eq" */
static const Nat sEq_items[] = {
  'E', 'q',
};
const Text sEq = {sEq_items, 2};

/* "refl" */
static const Nat srefl_items[] = {
  'r', 'e', 'f', 'l',
};
const Text srefl = {srefl_items, 4};

/* "transport" */
static const Nat stransport_items[] = {
  't', 'r', 'a', 'n', 's', 'p', 'o', 'r', 't',
};
const Text stransport = {stransport_items, 9};

/* "symm" */
static const Nat ssymm_items[] = {
  's', 'y', 'm', 'm',
};
const Text ssymm = {ssymm_items, 4};

/* "trans" */
static const Nat strans_items[] = {
  't', 'r', 'a', 'n', 's',
};
const Text strans = {strans_items, 5};

/* "cong" */
static const Nat scong_items[] = {
  'c', 'o', 'n', 'g',
};
const Text scong = {scong_items, 4};

/* "first" */
static const Nat sfirst_items[] = {
  'f', 'i', 'r', 's', 't',
};
const Text sfirst = {sfirst_items, 5};

/* "second" */
static const Nat ssecond_items[] = {
  's', 'e', 'c', 'o', 'n', 'd',
};
const Text ssecond = {ssecond_items, 6};

/* "either" */
static const Nat seither_items[] = {
  'e', 'i', 't', 'h', 'e', 'r',
};
const Text seither = {seither_items, 6};

/* "pure" */
static const Nat spure_items[] = {
  'p', 'u', 'r', 'e',
};
const Text spure = {spure_items, 4};

/* "map" */
static const Nat smap_items[] = {
  'm', 'a', 'p',
};
const Text smap = {smap_items, 3};

/* "bind" */
static const Nat sbind_items[] = {
  'b', 'i', 'n', 'd',
};
const Text sbind = {sbind_items, 4};

/* "fold" */
static const Nat sfold_items[] = {
  'f', 'o', 'l', 'd',
};
const Text sfold = {sfold_items, 4};

/* "unfold" */
static const Nat sunfold_items[] = {
  'u', 'n', 'f', 'o', 'l', 'd',
};
const Text sunfold = {sunfold_items, 6};

/* "filter" */
static const Nat sfilter_items[] = {
  'f', 'i', 'l', 't', 'e', 'r',
};
const Text sfilter = {sfilter_items, 6};

/* "Type 0" */
static const Nat sType0_items[] = {
  'T', 'y', 'p', 'e', ' ', '0',
};
const Text sType0 = {sType0_items, 6};

/* "Type 1" */
static const Nat sType1_items[] = {
  'T', 'y', 'p', 'e', ' ', '1',
};
const Text sType1 = {sType1_items, 6};

/* "cannot infer the type of this term" */
static const Nat eInfer_items[] = {
  'c', 'a', 'n', 'n', 'o', 't', ' ', 'i', 'n', 'f', 'e', 'r', ' ', 't', 'h', 'e', ' ', 't', 'y',
  'p', 'e', ' ', 'o', 'f', ' ', 't', 'h', 'i', 's', ' ', 't', 'e', 'r', 'm',
};
const Text eInfer = {eInfer_items, 34};

/* "expected a term of a product type" */
static const Nat eProduct_items[] = {
  'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 'a', ' ', 't', 'e', 'r', 'm', ' ', 'o', 'f', ' ',
  'a', ' ', 'p', 'r', 'o', 'd', 'u', 'c', 't', ' ', 't', 'y', 'p', 'e',
};
const Text eProduct = {eProduct_items, 33};

/* "type is not in the declared universe" */
static const Nat eUniverse_items[] = {
  't', 'y', 'p', 'e', ' ', 'i', 's', ' ', 'n', 'o', 't', ' ', 'i', 'n', ' ', 't', 'h', 'e', ' ',
  'd', 'e', 'c', 'l', 'a', 'r', 'e', 'd', ' ', 'u', 'n', 'i', 'v', 'e', 'r', 's', 'e',
};
const Text eUniverse = {eUniverse_items, 36};

/* "expected a data type" */
static const Nat eData_items[] = {
  'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 'a', ' ', 'd', 'a', 't', 'a', ' ', 't', 'y', 'p',
  'e',
};
const Text eData = {eData_items, 20};

/* "refl needs two equal sides" */
static const Nat eRefl_items[] = {
  'r', 'e', 'f', 'l', ' ', 'n', 'e', 'e', 'd', 's', ' ', 't', 'w', 'o', ' ', 'e', 'q', 'u', 'a',
  'l', ' ', 's', 'i', 'd', 'e', 's',
};
const Text eRefl = {eRefl_items, 26};

/* "expected an equality proof" */
static const Nat eProof_items[] = {
  'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 'a', 'n', ' ', 'e', 'q', 'u', 'a', 'l', 'i', 't',
  'y', ' ', 'p', 'r', 'o', 'o', 'f',
};
const Text eProof = {eProof_items, 26};

/* "trans needs the same middle value" */
static const Nat eTrans_items[] = {
  't', 'r', 'a', 'n', 's', ' ', 'n', 'e', 'e', 'd', 's', ' ', 't', 'h', 'e', ' ', 's', 'a', 'm',
  'e', ' ', 'm', 'i', 'd', 'd', 'l', 'e', ' ', 'v', 'a', 'l', 'u', 'e',
};
const Text eTrans = {eTrans_items, 33};

/* "expected fun with the declared parameters" */
static const Nat eFun_items[] = {
  'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 'f', 'u', 'n', ' ', 'w', 'i', 't', 'h', ' ', 't',
  'h', 'e', ' ', 'd', 'e', 'c', 'l', 'a', 'r', 'e', 'd', ' ', 'p', 'a', 'r', 'a', 'm', 'e', 't',
  'e', 'r', 's',
};
const Text eFun = {eFun_items, 41};

/* "work budget exceeded" */
static const Nat eBudget_items[] = {
  'w', 'o', 'r', 'k', ' ', 'b', 'u', 'd', 'g', 'e', 't', ' ', 'e', 'x', 'c', 'e', 'e', 'd', 'e',
  'd',
};
const Text eBudget = {eBudget_items, 20};

/* "the type has no instance of this structure" */
static const Nat eStructure_items[] = {
  't', 'h', 'e', ' ', 't', 'y', 'p', 'e', ' ', 'h', 'a', 's', ' ', 'n', 'o', ' ', 'i', 'n', 's',
  't', 'a', 'n', 'c', 'e', ' ', 'o', 'f', ' ', 't', 'h', 'i', 's', ' ', 's', 't', 'r', 'u', 'c',
  't', 'u', 'r', 'e',
};
const Text eStructure = {eStructure_items, 42};

/* "expected a function with one parameter" */
static const Nat eUnary_items[] = {
  'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 'a', ' ', 'f', 'u', 'n', 'c', 't', 'i', 'o', 'n',
  ' ', 'w', 'i', 't', 'h', ' ', 'o', 'n', 'e', ' ', 'p', 'a', 'r', 'a', 'm', 'e', 't', 'e', 'r',
};
const Text eUnary = {eUnary_items, 38};

/* "expected the name of a function" */
static const Nat eStep_items[] = {
  'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', ' ', 't', 'h', 'e', ' ', 'n', 'a', 'm', 'e', ' ', 'o',
  'f', ' ', 'a', ' ', 'f', 'u', 'n', 'c', 't', 'i', 'o', 'n',
};
const Text eStep = {eStep_items, 31};

/* "the number of functions does not fit the source of this fold" */
static const Nat eCases_items[] = {
  't', 'h', 'e', ' ', 'n', 'u', 'm', 'b', 'e', 'r', ' ', 'o', 'f', ' ', 'f', 'u', 'n', 'c', 't',
  'i', 'o', 'n', 's', ' ', 'd', 'o', 'e', 's', ' ', 'n', 'o', 't', ' ', 'f', 'i', 't', ' ', 't',
  'h', 'e', ' ', 's', 'o', 'u', 'r', 'c', 'e', ' ', 'o', 'f', ' ', 't', 'h', 'i', 's', ' ', 'f',
  'o', 'l', 'd',
};
const Text eCases = {eCases_items, 60};

/* "type parameters must come first" */
static const Nat eTypeParam_items[] = {
  't', 'y', 'p', 'e', ' ', 'p', 'a', 'r', 'a', 'm', 'e', 't', 'e', 'r', 's', ' ', 'm', 'u', 's',
  't', ' ', 'c', 'o', 'm', 'e', ' ', 'f', 'i', 'r', 's', 't',
};
const Text eTypeParam = {eTypeParam_items, 31};

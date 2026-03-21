#include "automapper.hpp"
#include <algorithm>
#include <cmath>
#include <cstdio>
#include <cstring>
#include <limits>
#include <unordered_map>
#include <vector>

static const char* OP_NAMES[] = {
    "NOP","BREAK","LOADNIL","LOADB","LOADN","LOADK","MOVE",
    "GETGLOBAL","SETGLOBAL","GETUPVAL","SETUPVAL","CLOSEUPVALS",
    "GETIMPORT","GETTABLE","SETTABLE","GETTABLEKS","SETTABLEKS",
    "GETTABLEN","SETTABLEN","NEWCLOSURE","NAMECALL","CALL","RETURN",
    "JUMP","JUMPBACK","JUMPIF","JUMPIFNOT",
    "JUMPIFEQ","JUMPIFLE","JUMPIFLT","JUMPIFNOTEQ","JUMPIFNOTLE","JUMPIFNOTLT",
    "ADD","SUB","MUL","DIV","MOD","POW",
    "ADDK","SUBK","MULK","DIVK","MODK","POWK",
    "AND","OR","ANDK","ORK",
    "CONCAT","NOT","MINUS","LENGTH",
    "NEWTABLE","DUPTABLE","SETLIST",
    "FORNPREP","FORNLOOP","FORGLOOP","FORGPREP_INEXT",
    "FASTCALL3","FORGPREP_NEXT","NATIVECALL",
    "GETVARARGS","DUPCLOSURE","PREPVARARGS","LOADKX",
    "JUMPX","FASTCALL","COVERAGE","CAPTURE",
    "SUBRK","DIVRK","FASTCALL1","FASTCALL2","FASTCALL2K",
    "FORGPREP",
    "JUMPXEQKNIL","JUMPXEQKB","JUMPXEQKN","JUMPXEQKS",
    "IDIV","IDIVK",
};

const char* stdOpName(int op) {
    if (op >= 0 && op < OP_COUNT) return OP_NAMES[op];
    return "???";
}

void OpcodeMap::assign(int shuffled, int standard, float conf) {
    if (shuffled < 0 || shuffled > 255) return;
    if (toStd[shuffled] != OP_UNKNOWN) return;
    if (standard >= 0 && standard < 256 && fromStd[standard] != -1) return;
    toStd[shuffled] = standard;
    confidence[shuffled] = conf;
    if (standard >= 0 && standard < 256) fromStd[standard] = shuffled;
    totalMapped++;
}

namespace {
struct MappingMetrics {
    int key = -1;
    int sampledFunctions = 0;
    int functionsWithReturn = 0;
    int totalWords = 0;
    int decodedOps = 0;
    int unknownOps = 0;
    int invalidAux = 0;
    int validJumpTargets = 0;
    int invalidJumpTargets = 0;
    int returnOps = 0;
    int callOps = 0;
    int namecallOps = 0;
    int conditionalOps = 0;
    double score = -std::numeric_limits<double>::infinity();
    double confidence = 0.0;
    std::unordered_map<int, int> opFrequency;
};

static bool opcodeHasAuxWord(int stdOp) {
    switch (stdOp) {
        case OP_GETIMPORT:
        case OP_GETGLOBAL:
        case OP_SETGLOBAL:
        case OP_GETTABLEKS:
        case OP_SETTABLEKS:
        case OP_NAMECALL:
        case OP_JUMPIFEQ:
        case OP_JUMPIFNOTEQ:
        case OP_JUMPIFLE:
        case OP_JUMPIFLT:
        case OP_JUMPIFNOTLE:
        case OP_JUMPIFNOTLT:
        case OP_LOADKX:
        case OP_NEWTABLE:
        case OP_SETLIST:
        case OP_FORGLOOP:
        case OP_FASTCALL3:
        case OP_FASTCALL2:
        case OP_FASTCALL2K:
        case OP_COVERAGE:
        case OP_JUMPXEQKNIL:
        case OP_JUMPXEQKB:
        case OP_JUMPXEQKN:
        case OP_JUMPXEQKS:
            return true;
        default:
            return false;
    }
}

static bool isConditionalJumpOp(int stdOp) {
    switch (stdOp) {
        case OP_JUMPIF:
        case OP_JUMPIFNOT:
        case OP_JUMPIFEQ:
        case OP_JUMPIFNOTEQ:
        case OP_JUMPIFLE:
        case OP_JUMPIFLT:
        case OP_JUMPIFNOTLE:
        case OP_JUMPIFNOTLT:
        case OP_JUMPXEQKNIL:
        case OP_JUMPXEQKB:
        case OP_JUMPXEQKN:
        case OP_JUMPXEQKS:
            return true;
        default:
            return false;
    }
}

static bool isJumpLikeOp(int stdOp) {
    switch (stdOp) {
        case OP_JUMP:
        case OP_JUMPBACK:
        case OP_JUMPX:
        case OP_FORNPREP:
        case OP_FORNLOOP:
        case OP_FORGPREP:
        case OP_FORGPREP_NEXT:
        case OP_FORGPREP_INEXT:
        case OP_FORGLOOP:
            return true;
        default:
            return isConditionalJumpOp(stdOp);
    }
}

static int modInverse256(int value) {
    value &= 0xFF;
    if ((value & 1) == 0) {
        return -1;
    }
    for (int candidate = 1; candidate < 256; candidate += 2) {
        if (((value * candidate) & 0xFF) == 1) {
            return candidate;
        }
    }
    return -1;
}

static OpcodeMap mapForEncodeKey(int encodeKey) {
    OpcodeMap m;
    memset(m.toStd, -1, sizeof(m.toStd));
    memset(m.fromStd, -1, sizeof(m.fromStd));
    memset(m.confidence, 0, sizeof(m.confidence));
    m.totalMapped = 0;
    m.detectedEncodeKey = encodeKey;
    m.mappingConfidence = 0.0f;
    m.usedFallback = false;
    m.sampledFunctions = 0;
    m.unknownOps = 0;
    m.invalidAux = 0;
    m.invalidJumpTargets = 0;

    int inverseKey = modInverse256(encodeKey);
    if (inverseKey < 0) {
        return m;
    }

    for (int std = 0; std < OP_COUNT; ++std) {
        int shuffled = (std * inverseKey) & 0xFF;
        m.assign(shuffled, std, 0.0f);
    }

    return m;
}

static MappingMetrics evaluateMapping(const Chunk& chunk, const OpcodeMap& map, int key) {
    static constexpr int kMaxSampledFunctions = 12;
    static constexpr int kMaxWordsPerFunction = 4096;

    MappingMetrics metrics;
    metrics.key = key;
    metrics.score = 0.0;

    std::vector<const Function*> candidates;
    candidates.reserve(chunk.functions.size());
    for (const auto& function : chunk.functions) {
        if (!function.instructions.empty()) {
            candidates.push_back(&function);
        }
    }
    std::sort(candidates.begin(), candidates.end(), [](const Function* lhs, const Function* rhs) {
        return lhs->instructions.size() > rhs->instructions.size();
    });

    for (int i = 0; i < (int)candidates.size() && metrics.sampledFunctions < kMaxSampledFunctions; ++i) {
        const Function& function = *candidates[i];
        const int instructionCount = (int)function.instructions.size();
        int inspectedWords = 0;
        bool sawReturnInFunction = false;
        metrics.sampledFunctions++;

        for (int pc = 0; pc < instructionCount && inspectedWords < kMaxWordsPerFunction; ) {
            const RawInstruction& raw = function.instructions[pc];
            int stdOp = map.lookup(raw.opcode());
            metrics.totalWords++;
            inspectedWords++;

            if (stdOp < 0 || stdOp >= OP_COUNT) {
                metrics.unknownOps++;
                metrics.score -= 1.2;
                pc += 1;
                continue;
            }

            metrics.decodedOps++;
            metrics.opFrequency[stdOp]++;
            metrics.score += 1.0;

            int width = 1;
            if (opcodeHasAuxWord(stdOp)) {
                width = 2;
                if (pc + 1 >= instructionCount) {
                    metrics.invalidAux++;
                    metrics.score -= 4.0;
                    width = 1;
                } else {
                    metrics.totalWords++;
                    inspectedWords++;
                }
            }

            if (stdOp == OP_RETURN) {
                sawReturnInFunction = true;
                metrics.returnOps++;
                metrics.score += 1.1;
            } else if (stdOp == OP_CALL || stdOp == OP_NATIVECALL) {
                metrics.callOps++;
                metrics.score += 0.15;
            } else if (stdOp == OP_NAMECALL) {
                metrics.namecallOps++;
                metrics.score += 0.2;
            }

            if (isConditionalJumpOp(stdOp)) {
                metrics.conditionalOps++;
            }

            if (isJumpLikeOp(stdOp)) {
                int targetPc = (stdOp == OP_JUMPX) ? (pc + raw.e() + 1) : (pc + raw.d() + 1);
                if (targetPc >= 0 && targetPc < instructionCount) {
                    metrics.validJumpTargets++;
                    metrics.score += 0.65;
                } else {
                    metrics.invalidJumpTargets++;
                    metrics.score -= 3.5;
                }
            }

            pc += width;
        }

        if (sawReturnInFunction) {
            metrics.functionsWithReturn++;
        }
    }

    const double totalWords = std::max(1, metrics.totalWords);
    const double knownRatio = (double)metrics.decodedOps / totalWords;
    const double jumpChecks = std::max(1, metrics.validJumpTargets + metrics.invalidJumpTargets);
    const double jumpQuality = (double)metrics.validJumpTargets / jumpChecks;
    const double returnCoverage = (double)metrics.functionsWithReturn / std::max(1, metrics.sampledFunctions);
    const double semanticSignal = std::min(
        1.0,
        (double)(metrics.callOps + metrics.namecallOps + metrics.conditionalOps + metrics.returnOps) /
            std::max(4.0, (double)metrics.decodedOps * 0.35)
    );
    const double penaltyRatio = ((double)metrics.invalidAux + (double)metrics.invalidJumpTargets +
                                 (double)metrics.unknownOps * 0.25) /
        std::max(1.0, (double)metrics.decodedOps + (double)metrics.unknownOps);

    metrics.score += knownRatio * 120.0;
    metrics.score += jumpQuality * 45.0;
    metrics.score += returnCoverage * 30.0;
    metrics.score += semanticSignal * 20.0;
    metrics.score -= penaltyRatio * 90.0;

    double confidence = 0.35 * knownRatio + 0.25 * jumpQuality + 0.2 * returnCoverage + 0.2 * semanticSignal;
    confidence -= 0.4 * penaltyRatio;
    metrics.confidence = std::clamp(confidence, 0.0, 1.0);
    return metrics;
}

static void stampPerOpcodeConfidence(OpcodeMap& map, const MappingMetrics& metrics, double overallConfidence) {
    int maxFrequency = 0;
    for (const auto& [stdOp, count] : metrics.opFrequency) {
        (void)stdOp;
        maxFrequency = std::max(maxFrequency, count);
    }

    for (int stdOp = 0; stdOp < OP_COUNT; ++stdOp) {
        int shuffled = map.fromStd[stdOp];
        if (shuffled < 0 || shuffled > 255) {
            continue;
        }
        const int observed = metrics.opFrequency.count(stdOp) ? metrics.opFrequency.at(stdOp) : 0;
        const double freqWeight = maxFrequency > 0 ? (double)observed / (double)maxFrequency : 0.0;
        const double opConfidence = std::clamp(overallConfidence * (0.6 + 0.4 * freqWeight), 0.05, 1.0);
        map.confidence[shuffled] = (float)opConfidence;
    }
}
} // namespace

OpcodeMap autoDetectOpcodes(const Chunk& chunk) {
    static constexpr int kPreferredKey = 203;
    static constexpr double kFastPathConfidence = 0.92;
    static constexpr double kFallbackConfidence = 0.55;

    std::vector<int> candidateKeys;
    candidateKeys.reserve(128);
    candidateKeys.push_back(kPreferredKey);
    for (int key = 1; key < 256; key += 2) {
        if (key != kPreferredKey) {
            candidateKeys.push_back(key);
        }
    }

    MappingMetrics bestMetrics;
    MappingMetrics secondMetrics;
    bestMetrics.score = -std::numeric_limits<double>::infinity();
    secondMetrics.score = -std::numeric_limits<double>::infinity();
    OpcodeMap bestMap;

    bool evaluatedAllCandidates = false;
    for (size_t i = 0; i < candidateKeys.size(); ++i) {
        const int key = candidateKeys[i];
        OpcodeMap candidateMap = mapForEncodeKey(key);
        if (candidateMap.totalMapped < OP_COUNT) {
            continue;
        }

        MappingMetrics metrics = evaluateMapping(chunk, candidateMap, key);
        if (metrics.score > bestMetrics.score) {
            secondMetrics = bestMetrics;
            bestMetrics = metrics;
            bestMap = candidateMap;
        } else if (metrics.score > secondMetrics.score) {
            secondMetrics = metrics;
        }

        if (i == 0 && metrics.confidence >= kFastPathConfidence) {
            evaluatedAllCandidates = false;
            break;
        }
        if (i + 1 == candidateKeys.size()) {
            evaluatedAllCandidates = true;
        }
    }

    if (bestMap.totalMapped < OP_COUNT) {
        bestMap = mapForEncodeKey(kPreferredKey);
        bestMetrics = evaluateMapping(chunk, bestMap, kPreferredKey);
        secondMetrics = {};
    }

    if (bestMetrics.score == -std::numeric_limits<double>::infinity()) {
        bestMap = mapForEncodeKey(kPreferredKey);
        bestMetrics = evaluateMapping(chunk, bestMap, kPreferredKey);
        secondMetrics = {};
    }

    double marginFactor = 1.0;
    if (std::isfinite(secondMetrics.score)) {
        double denom = std::max(1.0, std::fabs(bestMetrics.score));
        double margin = std::max(0.0, (bestMetrics.score - secondMetrics.score) / denom);
        marginFactor = std::clamp(0.55 + margin * 1.5, 0.55, 1.0);
    }

    bool usedFallback = false;
    double overallConfidence = std::clamp(bestMetrics.confidence * marginFactor, 0.0, 1.0);
    if (overallConfidence < kFallbackConfidence && bestMetrics.key != kPreferredKey) {
        OpcodeMap preferredMap = mapForEncodeKey(kPreferredKey);
        MappingMetrics preferredMetrics = evaluateMapping(chunk, preferredMap, kPreferredKey);
        if (preferredMetrics.score >= bestMetrics.score * 0.9) {
            bestMap = preferredMap;
            bestMetrics = preferredMetrics;
            overallConfidence = std::clamp(preferredMetrics.confidence, 0.0, 1.0);
            usedFallback = true;
        }
    }

    stampPerOpcodeConfidence(bestMap, bestMetrics, overallConfidence);
    bestMap.detectedEncodeKey = bestMetrics.key;
    bestMap.mappingConfidence = (float)overallConfidence;
    bestMap.usedFallback = usedFallback;
    bestMap.sampledFunctions = bestMetrics.sampledFunctions;
    bestMap.unknownOps = bestMetrics.unknownOps;
    bestMap.invalidAux = bestMetrics.invalidAux;
    bestMap.invalidJumpTargets = bestMetrics.invalidJumpTargets;

    fprintf(
        stderr,
        "[mapper] key=%d confidence=%.3f mapped=%d/%d sampled_functions=%d unknown=%d invalid_aux=%d invalid_jump=%d%s%s\n",
        bestMap.detectedEncodeKey,
        bestMap.mappingConfidence,
        bestMap.totalMapped,
        OP_COUNT,
        bestMetrics.sampledFunctions,
        bestMetrics.unknownOps,
        bestMetrics.invalidAux,
        bestMetrics.invalidJumpTargets,
        usedFallback ? " fallback=preferred_key" : "",
        evaluatedAllCandidates ? " mode=exhaustive" : " mode=fast"
    );

    fprintf(stderr, "[mapper] LOADK=%d NAMECALL=%d CALL=%d RETURN=%d GETIMPORT=%d GETTABLEKS=%d SETTABLEKS=%d\n",
        bestMap.fromStd[OP_LOADK],
        bestMap.fromStd[OP_NAMECALL],
        bestMap.fromStd[OP_CALL],
        bestMap.fromStd[OP_RETURN],
        bestMap.fromStd[OP_GETIMPORT],
        bestMap.fromStd[OP_GETTABLEKS],
        bestMap.fromStd[OP_SETTABLEKS]
    );

    return bestMap;
}

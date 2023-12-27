"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.joinWords = exports.wordsContain = exports.splitWords = exports.replaceWords = exports.substitute = void 0;
var DEBUG = true; // turn this to 'false' later if you want to prevent
// the CheckInv functions from executing. For this project you don't need to change it
// to false, but in a bigger program we might want to turn it off after debugging is
// complete, to avoid running expensive invariant checks when the project is released.
/**
 * Modifies the input array words by replacing with their corresponding
 * replacements from the reps
 *
 * @param words - An array of words to be modified.
 * @param reps-  A map from words to their replacements.
 * @modifies  words to substitute words according to reps.
 */
function substitute(words, reps) {
    var j = 0;
    var leng = words.length;
    while (j < leng) {
        var curWord = words[j];
        var replace = reps.get(curWord);
        if (typeof replace === 'string') {
            words[j] = replace;
        }
        j++;
    }
}
exports.substitute = substitute;
/**
 * Returns the list of words that results when each of the words in the given
 * map is replaced by its value, which can be multiple words.
 * @param words initial list of words
 * @param replacements map from strings to their replacements
 * @returns join(map(words, replacement)),
 *     where map(nil, reps) = nil
 *           map(cons(w, L), reps)) = reps.get(w) if w in reps
 *                                  = [w]         if w not in reps
 *     where join([]) = []
 *           join(L @ []) = join(L)
 *           join(L @ [S @ [w]]) = join(L @ S) @ [w]
 */
function replaceWords(words, replacements) {
    var replaced = [];
    var i = 0;
    // Inv: replaced[0..i-1] = map(words[0..i-1], replacements) and
    //      replaced[i..n-1] is unchanged
    while (i !== words.length) {
        var val = replacements.get(words[i]);
        if (val !== undefined) {
            replaced.push(val);
        }
        else {
            replaced.push([words[i]]);
        }
        i = i + 1;
    }
    var result = [];
    var j = 0;
    // Inv: result = join(replaced[0..j-1])
    while (j !== replaced.length) {
        var L = replaced[j];
        var k = 0;
        // Inv: result = join(replaced[0..j-1]) @ L[0..k-1]
        while (k !== L.length) {
            result.push(L[k]);
            k = k + 1;
        }
        j = j + 1;
    }
    return result;
}
exports.replaceWords = replaceWords;
// String containing all punctuation characters.
var PUNCT = ",.?;:!";
// Determines whether ch is a punctuation character.
function isPunct(ch) {
    if (ch.length !== 1)
        throw new Error("expecting a single character not \"".concat(ch, "\""));
    return PUNCT.indexOf(ch) >= 0;
}
/**
 * Breaks the given string into a sequence of words, separated by spaces or
 * punctuation. Spaces are not included in the result. Punctuation is included
 * as its own word.
 * @param str the string in question
 * @return an array of strings words such that
 *     1. join(words) = del-spaces(str), i.e., the concatenation of all the
 *        words is str but with all whitespace removed
 *     2. adjacent letters in the original string are in the same word
 *     3. no word includes any whitespace
 *     4. each word is either a single punctuation character or 1+ letters
 */
function splitWords(str) {
    var splits = [0]; // TODO (part a): fix this
    var j = 0; // TODO (part a): fix this
    CheckInv1(splits, str, j);
    // Inv  1. 0 = splits[0] < splits[1] < ... < splits[n] = j
    //      2. for i = 0 .. n-1, if splits[i+1] - splits[i] > 1, then
    //         str[splits[i] ..  splits[i+1]-1] is all letters
    //      3. for i = 1 .. n-1, splits[i] is not between two letters
    //  where n = parts.length
    while (j < str.length) {
        if (j === 0) {
            splits.push(1);
        }
        else {
            if (str[j] === " " || str[j - 1] == " ") {
                splits.push(j + 1);
            }
            else if (isPunct(str[j]) || isPunct(str[j - 1])) {
                splits.push(j + 1);
            }
            else {
                var temp = splits.length - 1;
                splits[temp] = j + 1;
            }
        }
        j++;
        CheckInv1(splits, str, j);
    }
    var words = [];
    var i = 0;
    CheckInv2(words, splits, str, i);
    // Inv: 1. join(words) = del-space(s[0..splits[i]-1]))
    //      2. no element of words contains any whitespace
    while (i + 1 !== splits.length) {
        if (str[splits[i]] !== " ")
            words.push(str.substring(splits[i], splits[i + 1]));
        i = i + 1;
        CheckInv2(words, splits, str, i);
    }
    // Post: join(words) = del-space(str), each punctuation is its own word,
    //       adjacent letters are in the same word, and no word has spaces
    return words;
}
exports.splitWords = splitWords;
// Verify that the invariant from the first loop of splitWords holds.
function CheckInv1(splits, str, j) {
    if (!DEBUG)
        return; // skip this
    if (splits.length === 0 || splits[0] !== 0)
        throw new Error("splits should start with 0");
    if (splits[splits.length - 1] !== j)
        throw new Error("splits should end with the string's length ".concat(j));
    var n = splits.length - 1;
    for (var i = 0; i < n; i++) {
        if (splits[i + 1] - splits[i] <= 0)
            throw new Error("should have at least 1 char between splits at ".concat(splits[i], " and ").concat(splits[i + 1]));
        var w = str.substring(splits[i], splits[i + 1]);
        if (w.length > 1) {
            for (var j_1 = 0; j_1 < w.length; j_1++) {
                if (w[j_1] === " " || isPunct(w[j_1]))
                    throw new Error("space/punct \"".concat(w[j_1], "\" is in a part with other characters"));
            }
        }
        if (i > 0) {
            var c1 = str[splits[i] - 1];
            var c2 = str[splits[i]];
            if ((c1 !== " ") && !isPunct(c1) && (c2 !== " ") && !isPunct(c2))
                throw new Error("split at ".concat(splits[i], " is between two letters \"").concat(c1, "\" and \"").concat(c2, "\""));
        }
    }
}
// Verify that the invariant from the second loop of splitWords holds.
function CheckInv2(words, splits, str, i) {
    if (!DEBUG)
        return; // skip this
    var s1 = words.join("");
    if (s1.indexOf(" ") >= 0)
        throw new Error("words contains space charactrs: \"".concat(s1, "\""));
    var s2 = str.slice(0, splits[i]);
    while (s2.indexOf(" ") >= 0)
        s2 = s2.replace(" ", "");
    if (s1 !== s2)
        throw new Error("words do not match the string (minus spaces): \"".concat(s1, "\" vs \"").concat(s2, "\""));
}
/**
 * Finds where the words of "sub" appear as a sub-array within "all".
 * @param all full list of words
 * @param sub non-empty list of words to search for in all
 * @returns an index j <= all.length - sub.length such that
 *     lower(all[j+i]) = lower(sub[i]) for i = 0 .. sub.length - 1
 *     or -1 if none exists
 */
function wordsContain(all, sub) {
    if (sub.length === 0)
        throw new Error("second list of words cannot be empty");
    if (all.length < sub.length)
        return -1; // not enough words to contain sub
    var k = -1;
    // Inv: no index 0 <= j <= k such that
    //      lower(all[j+i]) = lower(sub[i]) for i = 0 .. sub.length-1
    while (k + sub.length !== all.length) {
        k = k + 1;
        var m = 0;
        // Inv2: Inv and lower(all[k+i]) = lower(sub[i]) for i = 0 .. m-1
        while (m !== sub.length && all[k + m].toLowerCase() === sub[m].toLowerCase()) {
            m = m + 1;
        }
        if (m === sub.length) {
            // all[k+i] = sub[i] for i = 0 .. sub.length-1
            return k; // j = k matches
        }
    }
    // Post: no index 0 <= j <= all.length - sub.length such that
    //       all[j+i] = sub[i] for i = 0 .. sub.length-1
    return -1;
}
exports.wordsContain = wordsContain;
/**
 * Returns a string containing all of the given words, in the same order, but
 * with spaces before each (non-punctuation) word other than the first.
 * @param words list of words (no spaces, punctuation as its own words)
 * @return join-words(words), where
 *     join-words([]) = []
 *     join-words([w]) = w
 *     join-words(L @ [v, w]) =
 *         join-words(L @ [v]) + w        if w is punctuation
 *         join-words(L @ [v]) + " " + w  if w is not punctuation
 */
function joinWords(words) {
    if (words.length === 0) {
        return "";
    }
    var j = 0;
    var parts = [words[0]];
    for (j = 1; j < words.length; j++) {
        if (isPunct(words[j][0])) {
            parts.push(words[j]);
        }
        else {
            parts.push(" " + words[j]);
        }
    }
    return parts.join("");
}
exports.joinWords = joinWords;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoid29yZHMuanMiLCJzb3VyY2VSb290IjoiIiwic291cmNlcyI6WyIuLi9zcmMvd29yZHMudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6Ijs7O0FBQUEsSUFBTSxLQUFLLEdBQVksSUFBSSxDQUFDLENBQUUsb0RBQW9EO0FBQ2xGLHNGQUFzRjtBQUN0RixvRkFBb0Y7QUFDcEYsc0ZBQXNGO0FBRXRGOzs7Ozs7O0dBT0c7QUFDSCxTQUFnQixVQUFVLENBQUMsS0FBZSxFQUFFLElBQXlCO0lBQ25FLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQztJQUNWLElBQU0sSUFBSSxHQUFHLEtBQUssQ0FBQyxNQUFNLENBQUM7SUFDMUIsT0FBTyxDQUFDLEdBQUcsSUFBSSxFQUFFO1FBQ2YsSUFBTSxPQUFPLEdBQUcsS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDO1FBQ3pCLElBQU0sT0FBTyxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsT0FBTyxDQUFDLENBQUM7UUFDbEMsSUFBSSxPQUFPLE9BQU8sS0FBSyxRQUFRLEVBQUU7WUFDL0IsS0FBSyxDQUFDLENBQUMsQ0FBQyxHQUFHLE9BQU8sQ0FBQztTQUNwQjtRQUNELENBQUMsRUFBRSxDQUFDO0tBQ0w7QUFDSCxDQUFDO0FBWEQsZ0NBV0M7QUFFRDs7Ozs7Ozs7Ozs7O0dBWUc7QUFDSCxTQUFnQixZQUFZLENBQ3hCLEtBQTRCLEVBQzVCLFlBQWdEO0lBRWxELElBQU0sUUFBUSxHQUE0QixFQUFFLENBQUM7SUFDN0MsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO0lBRVYsK0RBQStEO0lBQy9ELHFDQUFxQztJQUNyQyxPQUFPLENBQUMsS0FBSyxLQUFLLENBQUMsTUFBTSxFQUFFO1FBQ3pCLElBQU0sR0FBRyxHQUFHLFlBQVksQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7UUFDdkMsSUFBSSxHQUFHLEtBQUssU0FBUyxFQUFFO1lBQ3JCLFFBQVEsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENB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
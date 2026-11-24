read("experiments/round-1.gp");
read("experiments/round-2.gp");

if(checkWalks() != [120,108,111,113], error("square walks"));
if(checkSharedPowers() != [20,68,105,112,113], error("shared powers"));
if(checkSieve() != [572,275,225], error("sieve"));
if(checkOrderRoutes() != [[1308,436],29], error("order routes"));
if(checkMoments() != 63, error("moments"));
if(checkOddDifferences() != [13384,113], error("odd differences"));

checkEqualOrders();
checkTwists();
checkAdaptiveTwists();
if(checkRectangles() != 3670, error("order rectangles"));
checkProgressions();
if(checkTransforms() != [2,6,70], error("transforms"));
coefficientCut(13,7,1);
coefficientCut(41,7,5);
coefficientCut(83,7,1);
checkDeepRoot();
checkFaithfulCut();
checkEventRanks(1);
if(checkConvexCuts() != [360,24,5400,65,65536,3870], error("convex cuts"));
print("PARI/GP checks passed");

all: base interval integers pi1s1 truncation freegroup wedgecircles pullback pushout

base:
	agda Base.agda

interval:
	agda Interval/IntervalProps.agda

integers:
	agda Integers/Integers.agda

pi1s1:
	agda Circle/LoopSpace.agda

truncation:
	agda Truncation/TruncatedHIT.agda
	agda Truncation/Truncation.agda

freegroup:
	agda FreeGroup/FreeGroup.agda
	agda FreeGroup/FreeGroupProps.agda
	agda FreeGroup/F2NotCommutative.agda

wedgecircles:
	agda WedgeCircles/LoopSpaceWedgeCircles2.agda

pullback:
	agda CategoryTheory/PullbackDef.agda
	agda CategoryTheory/PullbackIsPullback.agda
	agda CategoryTheory/PullbackUP.agda

pushout:
	agda CategoryTheory/PushoutDef.agda
	agda CategoryTheory/PushoutIsPushout.agda
	agda CategoryTheory/PushoutUP.agda


clean:
	rm *.agdai */*.agdai

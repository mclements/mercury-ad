mlp_R:
	mmc --make mlp_R libad && ./mlp_R

test:
	mmc --make test_ad libad && ./test_ad


ifeq ($(OS),Windows_NT)
include Makefile.win32
else
include Makefile.x86_64
endif

GM_BIN=../gm.exe

THESIS=../reports/thesis_2010CSY7543

FIGURES=../reports/figures

SYNOPSIS=../reports/synopsis.tex

PRESENTATION_OLD=../reports/presentation.tex

PRESENTATION=../reports/presentation-final.tex

TEX_OUT_DIR=../reports
TEX_AUX_DIR=../reports
TEX_INC_DIR=../reports
COQDOC_OPTS= --latex --body-only --no-lib-name 

all : $(GM_BIN) certified reports 

$(GM_BIN) : *.hs
	$(GHC) --make Main -o $(GM_BIN)
	
reports_rm : verified/RM.v
	$(COQDOC) $(COQDOC_OPTS) -t "Register Machine" -o $(TEX_AUX_DIR)/_RM.tex verified/RM.v

reports_rmtest : verified/RMTest.v
	$(COQDOC) $(COQDOC_OPTS) -o $(TEX_AUX_DIR)/_RMTest.tex verified/RMTest.v

reports_h : verified/H.v
	$(COQDOC) $(COQDOC_OPTS) -o $(TEX_AUX_DIR)/_H.tex verified/H.v

reports_gm : verified/GM.v
	$(COQDOC) $(COQDOC_OPTS) -o $(TEX_AUX_DIR)/_GM.tex verified/GM.v

reports_gmtest : verified/GMTest.v
	$(COQDOC) $(COQDOC_OPTS) -o $(TEX_AUX_DIR)/_GMTest.tex verified/GMTest.v

reports_xlator : verified/Xlator.v
	$(COQDOC) $(COQDOC_OPTS) -o $(TEX_AUX_DIR)/_Xlator.tex verified/Xlator.v

reports_sflib : verified/SfLib.v
	$(COQDOC) $(COQDOC_OPTS) -o $(TEX_AUX_DIR)/_SfLib.tex verified/SfLib.v

reports_vheap: verified/VHeap.v
	$(COQDOC) $(COQDOC_OPTS) -o $(TEX_AUX_DIR)/_VHeap.tex verified/VHeap.v

reports_vtypes: verified/VTypes.v
	$(COQDOC) $(COQDOC_OPTS) -o $(TEX_AUX_DIR)/_VTypes.tex verified/VTypes.v

reports_vutils : verified/VUtils.v
	$(COQDOC) $(COQDOC_OPTS) -o $(TEX_AUX_DIR)/_VUtils.tex verified/VUtils.v

reports : reports_h \
		  reports_rm \
		  reports_gm \
		  reports_rmtest \
		  reports_gmtest \
		  reports_xlator \
		  reports_sflib \
		  reports_vtypes \
		  reports_vheap \
		  reports_vutils

# PICTURES
figures : 
	$(PDFLATEX) \
	-synctex=1 \
	-interaction=nonstopmode \
	-aux-directory=$(TEX_AUX_DIR) \
	-include-directory=$(TEX_INC_DIR) \
	-output-directory=$(TEX_OUT_DIR) \
	--src-specials $(FIGURES)
	
THESIS_GEN_CMD=$(PDFLATEX) \
	-synctex=1 \
	-interaction=nonstopmode \
	-aux-directory=$(TEX_AUX_DIR) \
	-include-directory=$(TEX_INC_DIR) \
	-output-directory=$(TEX_OUT_DIR) \
	--src-specials $(THESIS)

BIBTEX_GEN_CMD=$(BIBTEX) \
	-include-directory=../reports $(THESIS)

SYNOPSIS_GEN_CMD=$(PDFLATEX) \
	-synctex=1 \
	-interaction=nonstopmode \
	-aux-directory=$(TEX_AUX_DIR) \
	-include-directory=$(TEX_INC_DIR) \
	-output-directory=$(TEX_OUT_DIR) \
	--src-specials $(SYNOPSIS)
	
PRESENTATION_GEN_CMD=$(PDFLATEX) \
	-synctex=1 \
	-interaction=nonstopmode \
	-aux-directory=$(TEX_AUX_DIR) \
	-include-directory=$(TEX_INC_DIR) \
	-output-directory=$(TEX_OUT_DIR) \
	--src-specials $(PRESENTATION)	

# Need three latex runs for the passes
thesis : 
	$(THESIS_GEN_CMD) > out_pre.log
	$(BIBTEX_GEN_CMD) > out_bib.log
	$(THESIS_GEN_CMD) > out_post.log
	$(THESIS_GEN_CMD) > out.log
	
cover : 
	$(PDFLATEX) -synctex=1 \
	-interaction=nonstopmode \
	-aux-directory=$(TEX_AUX_DIR) \
	-include-directory=$(TEX_INC_DIR) \
	-output-directory=$(TEX_OUT_DIR) \
	--src-specials cover.tex

# this target is for checking compilation success
quick : 
	$(THESIS_GEN_CMD) > quick.log

synopsis : $(SYNOPSIS)
	$(SYNOPSIS_GEN_CMD)
	$(SYNOPSIS_GEN_CMD)
	$(SYNOPSIS_GEN_CMD)

presentation : $(PRESENTATION)
	$(PRESENTATION_GEN_CMD) > presentation_out.log

VSFLIB : verified/SfLib.vo

verified/SfLib.vo : verified/SfLib.v
	$(COQC) verified/SfLib.v

VTYPES : verified/VTypes.vo

verified/VTypes.vo : verified/VTypes.v
	$(COQC) verified/VTypes.v

VUTILS : verified/VUtils.vo

verified/VUtils.vo : verified/VUtils.v
	$(COQC) verified/VUtils.v

VRM : VTYPES VUTILS VHEAP VGM verified/RM.vo

verified/RM.vo : verified/RM.v
	$(COQC) verified/RM.v

VRMMU : VRM verified/RMMu.vo

verified/RMMu.vo : verified/RMMu.v
	$(COQC) verified/RMMu.v

VGM : VTYPES VUTILS verified/GM.vo

verified/GM.vo : verified/GM.v
	$(COQC) verified/GM.v

VXLATOR : VTYPES VUTILS VHEAP VGM VRM verified/Xlator.vo

verified/Xlator.vo : verified/Xlator.v
	$(COQC) verified/Xlator.v

VHEAP : VTYPES VUTILS verified/VHeap.vo

verified/VHeap.vo : verified/VHeap.v
	$(COQC) verified/VHeap.v
	
DUMMY.FILE :	

verified/FImplTest.v : $(GM_BIN) DUMMY.FILE 
	$(GM_BIN) -q ../testCases/$(CRFILE) >verified/FImplTest.v

verified/FImplTest.vo : verified/FImplTest.v
	$(COQC) verified/FImplTest.v

verified/RMOut.vo : verified/RMOut.v
	$(COQC) verified/RMOut.v

VGEN : verified/FImplTest.vo verified/RMOut.vo

VTEST : 
	$(COQC) verified/FImplTest.v
	$(COQC) verified/XlatorTest.v

VRUN : VGEN
	$(COQC) verified/XlatorDriver.v
    	
certified : VSFLIB VTYPES VUTILS VHEAP VGM VRM VXLATOR VRMMU

clean :
	rm -r -f $(GM_BIN) *.hi \
	*.o \
	*~ \
	verified/*.vo \
	verified/*.glob \
	../reports/_*.tex \
	../reports/*.aux \
	../reports/*.out \
	../reports/*.toc \
	../reports/*.log \
	../reports/*.synctex.gz \
	../reports/*.bbl

#!/usr/bin/env bash
set -u -o pipefail

ROOT="EML_NeuroCreativity_Preparation_Papers"
mkdir -p \
  "$ROOT/01_Core_Creative_Sensemaking" \
  "$ROOT/02_Enaction_and_CoCreative_AI" \
  "$ROOT/03_LuminAI_and_Embodied_CoCreativity" \
  "$ROOT/04_Motion_ML_and_Visualization" \
  "$ROOT/05_Improvisation_Foundations"

MANIFEST="$ROOT/download_manifest.tsv"
printf 'status\tfile\tsource_url\n' > "$MANIFEST"

download_pdf() {
  local url="$1"
  local out="$2"
  local tmp="${out}.part"
  mkdir -p "$(dirname "$out")"
  echo "Downloading $out"
  if curl -L --fail --silent --show-error \
      --retry 4 --retry-delay 2 --retry-all-errors \
      --connect-timeout 30 --max-time 420 \
      -A 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/125 Safari/537.36' \
      "$url" -o "$tmp"; then
    if [ "$(head -c 4 "$tmp" 2>/dev/null || true)" = "%PDF" ]; then
      mv "$tmp" "$out"
      printf 'downloaded\t%s\t%s\n' "${out#${ROOT}/}" "$url" >> "$MANIFEST"
      return 0
    fi
  fi
  rm -f "$tmp"
  printf 'failed\t%s\t%s\n' "${out#${ROOT}/}" "$url" >> "$MANIFEST"
  return 1
}

# Core participatory / creative sense-making
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2016/08/p196-davis_IUI.pdf' \
  "$ROOT/01_Core_Creative_Sensemaking/2016_Empirically_Studying_Participatory_Sense_Making.pdf" || true
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2016/08/CHAPTER.pdf' \
  "$ROOT/01_Core_Creative_Sensemaking/2015_An_Enactive_Model_of_Creativity_for_Computational_Collaboration.pdf" || true
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2016/08/p185-davis_DApp_CC.pdf' \
  "$ROOT/01_Core_Creative_Sensemaking/2015_The_Drawing_Apprentice.pdf" || true
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2016/08/p275-davis_play.pdf' \
  "$ROOT/01_Core_Creative_Sensemaking/2015_An_Enactive_Characterization_of_Pretend_Play.pdf" || true

# Enaction and computational co-creativity
download_pdf 'https://computationalcreativity.net/iccc2014/wp-content/uploads/2014/06/2.3_Davis.pdf' \
  "$ROOT/02_Enaction_and_CoCreative_AI/2014_Building_Artistic_Computer_Colleagues.pdf" || true
download_pdf 'https://computationalcreativity.net/iccc24/papers/ICCC24_paper_58.pdf' \
  "$ROOT/02_Enaction_and_CoCreative_AI/2024_The_Five_Pillars_of_Enaction.pdf" || true
download_pdf 'https://arxiv.org/pdf/2606.15358' \
  "$ROOT/02_Enaction_and_CoCreative_AI/2026_Cognitive_Trajectory_Modeling.pdf" || true
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2015/08/Jacob.ICCC15.Interaction-based.Authoring.for_.Scalable.Co-creative.Agents.pdf' \
  "$ROOT/02_Enaction_and_CoCreative_AI/2015_Interaction_Based_Authoring_for_Scalable_CoCreative_Agents.pdf" || true
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2009/02/Davis_Enactive-Interactive-Machine-Learning.pdf' \
  "$ROOT/02_Enaction_and_CoCreative_AI/Enactive_Interactive_Machine_Learning.pdf" || true

# LuminAI / Viewpoints AI and embodied co-creativity
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2013/10/Jacob.AIIDE13.Viewpoints.AI_.pdf' \
  "$ROOT/03_LuminAI_and_Embodied_CoCreativity/2013_Viewpoints_AI_AIIDE.pdf" || true
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2013/10/Jacob.DIGRA13.Viewpoints.AI_.pdf' \
  "$ROOT/03_LuminAI_and_Embodied_CoCreativity/2013_Viewpoints_AI_Procedural_Representation_and_Gesture_Meaning.pdf" || true
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2018/08/JacobMagerko.FDG18.CiG18.Creative.Arcs_.In_.Improvised.Human_.Computer.Embodied.Performances.pdf' \
  "$ROOT/03_LuminAI_and_Embodied_CoCreativity/2018_Creative_Arcs_in_Improvised_Human_Computer_Embodied_Performances.pdf" || true
download_pdf 'http://www.durilong.com/s/a5-liu.pdf' \
  "$ROOT/03_LuminAI_and_Embodied_CoCreativity/2019_Learning_Movement_through_Human_Computer_CoCreative_Improvisation.pdf" || true
download_pdf 'http://www.durilong.com/s/Designing_Co_Creative_AI_for_Public_Spaces-CAMERA-READY.pdf' \
  "$ROOT/03_LuminAI_and_Embodied_CoCreativity/2019_Designing_CoCreative_AI_for_Public_Spaces.pdf" || true
download_pdf 'http://www.durilong.com/s/Trajectories_of_Physical_Engagement_and_Expression_in_a_Co_Creative_Museum_Installation-CAMERA-READY.pdf' \
  "$ROOT/03_LuminAI_and_Embodied_CoCreativity/2019_Trajectories_of_Physical_Engagement_and_Expression.pdf" || true

# Motion ML
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2018/08/Singh.et_.al_.AIIDE16.Recognizing.Actions.In_.Motion.Trajectories.Using_.Deep_.Neural.Networks.pdf' \
  "$ROOT/04_Motion_ML_and_Visualization/2016_Recognizing_Actions_in_Motion_Trajectories_Using_DNNs.pdf" || true

# Human improvisation foundations
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2010/07/magerkocreativityandcognition2009.pdf' \
  "$ROOT/05_Improvisation_Foundations/2009_An_Empirical_Study_of_Cognition_and_Theatrical_Improvisation.pdf" || true
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2011/11/cceditedfinalsmmfuller.pdf' \
  "$ROOT/05_Improvisation_Foundations/2011_Shared_Mental_Models_in_Improvisational_Theatre.pdf" || true
download_pdf 'http://expressivemachinery.gatech.edu/wp-content/uploads/2010/04/medler-magerko-chi2010.pdf' \
  "$ROOT/05_Improvisation_Foundations/2010_Improvisational_Acting_and_Role_Playing_for_Design.pdf" || true

PDF_COUNT="$(find "$ROOT" -type f -name '*.pdf' | wc -l | tr -d ' ')"
FAILED_COUNT="$(awk -F '\t' '$1=="failed" {n++} END {print n+0}' "$MANIFEST")"

cat > "$ROOT/README.md" <<EOF
# EML NeuroCreativity / Neuroscience of Co-creativity preparation papers

This bundle contains publicly accessible papers selected for preparation for Brian Magerko's EML NeuroCreativity research project. It focuses on the conceptual and technical lineage most relevant to creative sense-making, enaction, embodied co-creativity, LuminAI/Viewpoints AI, movement representation/classification, and improvisational cognition.

## Recommended reading order

1. 2016 - Empirically Studying Participatory Sense-Making
2. 2015 - An Enactive Model of Creativity for Computational Collaboration and Co-Creation
3. 2024 - The Five Pillars of Enaction
4. 2018 - Creative Arcs in Improvised Human-Computer Embodied Performances
5. 2019 - Learning Movement through Human-Computer Co-Creative Improvisation
6. 2019 - Designing Co-Creative AI for Public Spaces
7. 2019 - Trajectories of Physical Engagement and Expression
8. 2016 - Recognizing Actions in Motion Trajectories Using Deep Neural Networks
9. 2009 - An Empirical Study of Cognition and Theatrical Improvisation
10. 2011 - Shared Mental Models in Improvisational Theatre

## Integrity and scope

- Every included document was checked for the PDF magic header before packaging.
- download_manifest.tsv records the source and retrieval status for every attempted file.
- SHA256SUMS.txt enables file-integrity verification.
- Publisher pages that returned HTML, access challenges, or non-PDF data were not disguised as PDFs.
- Valid PDF files included: ${PDF_COUNT}
- Automated retrieval failures: ${FAILED_COUNT}
EOF

find "$ROOT" -type f -name '*.pdf' -print0 | sort -z | xargs -0 sha256sum > "$ROOT/SHA256SUMS.txt"
find "$ROOT" -type f | sort > "$ROOT/CONTENTS.txt"

echo "Downloaded PDFs: $PDF_COUNT"
echo "Failed downloads: $FAILED_COUNT"
cat "$MANIFEST"

if [ "$PDF_COUNT" -lt 15 ]; then
  echo "Only $PDF_COUNT valid PDFs were retrieved; refusing to publish an incomplete bundle." >&2
  exit 1
fi

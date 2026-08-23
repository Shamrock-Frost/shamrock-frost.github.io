<?xml version="1.0"?>
<!-- Local overrides on the vendored base theme. See PROVENANCE.md.

     Note for editors: XML forbids a double hyphen inside a comment,
     so prose here uses an em dash. Getting that wrong does not break
     one page, it breaks all of them at once: the browser fails to
     parse the stylesheet and every node renders as raw XML.

     Forester 5.0 hardcodes the stylesheet name to default.xsl (the
     4.x forest.toml key is gone), so this file has to take that name
     and upstream's is vendored beside it as base.xsl — contents
     untouched, only the filename changed. This is the only file in
     theme/ that is ours; re-vendoring a later tag is a clean overwrite
     of everything else.

     One override. Every statement node carries \meta{status}{...}, and
     status is the single most useful thing to see when scanning fifty
     nodes — what is proven, what is conditional, what was refuted and
     is on the record anyway. Forester emits metas into the frontmatter
     but the base theme only renders the handful it knows (doi, orcid,
     venue…), so status would otherwise be invisible.

     It is deliberately styled with the theme's own .slug class rather
     than new CSS: the status then sits beside the [ffi-0043] address
     chip and inherits its colour, weight and dark-mode behaviour, and
     this file stays a template override instead of a fork.

     check-render.py asserts the status text reaches the rendered HTML,
     so if a future theme version renames the title template this fails
     the build instead of silently dropping the badge. -->
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:f="http://www.forester-notes.org">

  <!-- import, not include: imported templates lose to ours on a tie -->
  <xsl:import href="base.xsl" />

  <xsl:output method="html" encoding="utf-8" indent="yes"
    doctype-public="" doctype-system="" omit-xml-declaration="yes" />

  <xsl:template match="f:frontmatter/f:title">
    <xsl:apply-templates />
    <xsl:apply-templates select="../f:meta[@name='status']" mode="chip" />
  </xsl:template>

  <xsl:template match="f:meta" mode="chip">
    <xsl:text> </xsl:text>
    <span class="slug">
      <xsl:text>(</xsl:text>
      <xsl:value-of select="." />
      <xsl:text>)</xsl:text>
    </span>
  </xsl:template>

</xsl:stylesheet>

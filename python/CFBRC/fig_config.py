class FigConfig:
    """Configuration for figure generation."""

    debug = False

    def __init__(self, dpi=300, size=(10, 6)):
        self.dpi = dpi
        self.size = size
        self.release = False
        self.prefix_fig = "fig"
        self.prefix = self.prefix_fig if self.release else "__" + self.prefix_fig
        self.binom = True  # True: binomial, False: centered
        self.graph_version = "v1r1-" + ("b" if self.binom else "c") + f"-dpi{self.dpi}"
        self.show = True  # Whether to show plots interactively
        (
            print(
                f"FigConfig initialized: dpi={self.dpi}, size={self.size}, prefix='{self.prefix}', graph_version='{self.graph_version}', show={self.show}, binom={self.binom}"
            )
            if self.debug
            else None
        )

    def update_release(self, release):
        """Update the release setting and adjust related attributes."""
        self.release = release
        self.prefix = self.prefix_fig if self.release else "__" + self.prefix_fig
        (
            print(f"FigConfig updated: release={self.release}, prefix='{self.prefix}'")
            if self.debug
            else None
        )

    def update_binom(self, binom):
        """Update the binom setting and adjust related attributes."""
        self.binom = binom
        self.graph_version = "v1r1-" + ("b" if self.binom else "c") + f"-dpi{self.dpi}"
        (
            print(
                f"FigConfig updated: binom={self.binom}, graph_version='{self.graph_version}'"
            )
            if self.debug
            else None
        )

    def filename(self, label, dx):
        """Generate a filename based on the label and dx."""
        return f"{self.prefix}#{label}-{dx}-{self.graph_version}.png"


class Fig4Config(FigConfig):
    """Configuration for figures specific to experiment #4."""

    def __init__(self, dpi=300, size=(10, 6)):
        super().__init__(dpi, size)
        print("Fig4Config initialized.") if self.debug else None

    def filename(self, label, dx, binom=None):
        """Generate a filename specific to experiment #4."""
        if binom is not None:
            original_binom = self.binom
            self.update_binom(binom)
        filename = f"{self.prefix}#4-{label}-{dx}-{self.graph_version}.png"
        self.update_binom(original_binom)  # Restore original binom
        print(f"Fig4Config filename generated: {filename}") if self.debug or 1 else None
        return filename


fig_config = FigConfig()
fig4_config = Fig4Config()

# Usage example:
# plt.savefig(fig_config.filename("4-2_G_phase_vs_theta_unwrapped", dx), dpi=fig_dpi, bbox_inches="tight")

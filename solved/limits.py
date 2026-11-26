"""Resource stops shared by exact mathematical searches."""


class ResourceLimit(RuntimeError):
    """A resource budget was exhausted; this is not an infeasibility result."""

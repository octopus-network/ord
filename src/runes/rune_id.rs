use {super::*, std::num::TryFromIntError};

#[derive(Debug, PartialEq, Copy, Clone, Hash, Eq, Ord, PartialOrd)]
pub struct RuneId {
  pub height: u32,
  pub index: u16,
}

impl TryFrom<u128> for RuneId {
  type Error = TryFromIntError;

  fn try_from(n: u128) -> Result<Self, Self::Error> {
    Ok(Self {
      height: u32::try_from(n >> 16)?,
      index: u16::try_from(n & 0xFFFF).unwrap(),
    })
  }
}

impl From<RuneId> for u128 {
  fn from(id: RuneId) -> Self {
    u128::from(id.height) << 16 | u128::from(id.index)
  }
}

impl Display for RuneId {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    write!(f, "{}/{}", self.height, self.index,)
  }
}

impl FromStr for RuneId {
  type Err = crate::Error;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let (height, index) = s
      .split_once('/')
      .ok_or_else(|| anyhow!("invalid rune ID: {s}"))?;

    Ok(Self {
      height: height.parse()?,
      index: index.parse()?,
    })
  }
}

impl Serialize for RuneId {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    serializer.collect_str(self)
  }
}

impl<'de> Deserialize<'de> for RuneId {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    Ok(DeserializeFromStr::deserialize(deserializer)?.0)
  }
}

#[derive(Debug, Default, PartialEq, Copy, Clone, Hash, Eq, Ord, PartialOrd)]
pub struct HexRuneId {
  pub height: u32,
  pub index: u16,
}

impl Display for HexRuneId {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    let value = u128::from(self.height) << 16 | u128::from(self.index);
    write!(f, "{:x}", value)
  }
}

impl From<RuneId> for HexRuneId {
  fn from(id: RuneId) -> Self {
    Self {
      height: id.height,
      index: id.index,
    }
  }
}

impl From<HexRuneId> for RuneId {
  fn from(id: HexRuneId) -> Self {
    Self {
      height: id.height,
      index: id.index,
    }
  }
}

impl FromStr for HexRuneId {
  type Err = crate::Error;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let rune_id_u128 = u128::from_str_radix(s, 16)?;
    let rune_id = RuneId::try_from(rune_id_u128)?;

    Ok(Self {
      height: rune_id.height,
      index: rune_id.index,
    })
  }
}

impl Serialize for HexRuneId {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    serializer.collect_str(self)
  }
}

impl<'de> Deserialize<'de> for HexRuneId {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    Ok(DeserializeFromStr::deserialize(deserializer)?.0)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn rune_id_to_128() {
    assert_eq!(
      0b11_0000_0000_0000_0001u128,
      RuneId {
        height: 3,
        index: 1,
      }
      .into()
    );
  }

  #[test]
  fn display() {
    assert_eq!(
      RuneId {
        height: 1,
        index: 2
      }
      .to_string(),
      "1/2"
    );
  }

  #[test]
  fn from_str() {
    assert!("/".parse::<RuneId>().is_err());
    assert!("1/".parse::<RuneId>().is_err());
    assert!("/2".parse::<RuneId>().is_err());
    assert!("a/2".parse::<RuneId>().is_err());
    assert!("1/a".parse::<RuneId>().is_err());
    assert_eq!(
      "1/2".parse::<RuneId>().unwrap(),
      RuneId {
        height: 1,
        index: 2
      }
    );
  }

  #[test]
  fn try_from() {
    assert_eq!(
      RuneId::try_from(0x060504030201).unwrap(),
      RuneId {
        height: 0x06050403,
        index: 0x0201
      }
    );

    assert!(RuneId::try_from(0x07060504030201).is_err());
  }

  #[test]
  fn display_hex_rune_id() {
    let rune_id = RuneId {
      height: 0x06050403,
      index: 0x0201,
    };

    let rune_id_u128 = u128::from(rune_id);
    let hex_rune_id = format!("{:x}", rune_id_u128);
    assert_eq!(hex_rune_id, "60504030201");
  }

  #[test]
  fn from_str_hex_rune_id() {
    let hex_rune_id = "60504030201";
    let rune_id_u128 = u128::from_str_radix(hex_rune_id, 16).unwrap();
    let rune_id = RuneId::try_from(rune_id_u128).unwrap();
    assert_eq!(
      rune_id,
      RuneId {
        height: 0x06050403,
        index: 0x0201
      }
    );
    let hex_rune_id = "26be57000d";
    let rune_id_u128 = u128::from_str_radix(hex_rune_id, 16).unwrap();
    let rune_id = RuneId::try_from(rune_id_u128).unwrap();
    assert_eq!(
      rune_id,
      RuneId {
        height: 0x26be57,
        index: 0x000d
      }
    );
  }

  #[test]
  fn serde() {
    let rune_id = RuneId {
      height: 1,
      index: 2,
    };
    let json = "\"1/2\"";
    assert_eq!(serde_json::to_string(&rune_id).unwrap(), json);
    assert_eq!(serde_json::from_str::<RuneId>(json).unwrap(), rune_id);
  }
}
